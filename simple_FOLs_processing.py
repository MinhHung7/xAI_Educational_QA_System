import json
import z3
import re
import os
from collections import defaultdict
import sys
from test_parts_split import split_top_level
import regex
from collections import Counter
from flask import Flask, request, jsonify
from dotenv import load_dotenv
from flask_limiter import Limiter
from flask_limiter.util import get_remote_address


app = Flask(__name__)

# Setup rate limiter
limiter = Limiter(
    app,
    key_func=get_remote_address,  # identify users by IP address
    default_limits=["10 per second"]  # 10 requests per second
)

load_dotenv()  # Ensure environment variables are loaded from .env file
API_KEY = os.getenv("API_KEY")  # Read API_KEY from environment variables
PORT = os.getenv("PORT") or 8000  # Read PORT from environment variables

# Redirect stdout và stderr
log_file = open('simple_FOLs_logs.txt', 'w', encoding='utf-8')
sys.stdout = log_file
sys.stderr = log_file


# --- Hàm load JSON (từ lần trước) ---
def load_json_dataset(filepath):
    try:
        if not os.path.exists(filepath):
            print(f"Error: File not found at {filepath}")
            return None
        with open(filepath, 'r', encoding='utf-8') as f:
            data = json.load(f)
        print(f"Successfully loaded data from {filepath}")
        return data
    except Exception as e:
        print(f"An error occurred while loading {filepath}: {e}")
        return None


# --- 1. Khai báo Sorts và Predicates (Cần mở rộng dựa trên toàn bộ dataset) ---
# Giả định một Sort chung ban đầu. Bạn cần xem xét dataset để xác định các Sorts cần thiết.
Item = z3.DeclareSort('Item')
# x = z3.Const('x', Item) # Biến mặc định cho quantifiers

# Degree = z3.DeclareSort('Degree')
# d = z3.Const('d', Degree)
# BA = z3.Const('BA', Degree)

# Sử dụng defaultdict để tự động tạo predicate Z3 khi gặp tên mới
# Lưu ý: Cách này đơn giản nhưng giả định tất cả predicate có cùng cấu trúc (Item -> Bool)
# Bạn có thể cần logic phức tạp hơn nếu có predicate với nhiều đối số hoặc sort khác nhau.
# predicate_cache = defaultdict(lambda name: z3.Function(name, Item, z3.BoolSort()))

predicate_cache={}


# Định nghĩa trước signature cho các predicate đặc biệt
PREDEFINED_SIGNATURES = {
    # 'higher': (Item, Item, z3.BoolSort()),
    # 'has_degree': (Item, Item, z3.BoolSort()), # Giả định: người, bằng cấp -> bool
    # 'before': (Item, z3.Item)
    # Thêm các predicate khác nếu cần, ví dụ:
    # 'completed_courses': (Item, z3.IntSort(), z3.BoolSort()), # Nếu có so sánh số lượng
    # 'gpa_above_3_5': (Item, z3.BoolSort()), # Đã có trong regex

}

def get_predicate(name, *arg_sorts_for_inference):
    """
    Lấy hoặc tạo predicate Z3. Ưu tiên signature định nghĩa trước.
    Nếu không có, thử suy luận signature dựa trên sort của đối số mẫu được truyền vào.
    """
    print(name)
    print("OK")
    clean_name = name.strip()
    if not clean_name:
        raise ValueError("Predicate name cannot be empty")
    
    arity = len(arg_sorts_for_inference)
    cache_key = (clean_name, arity)

    if cache_key not in predicate_cache:
        print(f"  Defining Predicate: {clean_name} with arity {arity}")

        if clean_name in PREDEFINED_SIGNATURES:
            sig = PREDEFINED_SIGNATURES[clean_name]
            print(f"    Using predefined signature: {[s.name() for s in sig[:-1]]} -> {sig[-1].name()}")
            predicate_cache[cache_key] = z3.Function(clean_name, *sig)
        else:
            # -------------------------------------
            num_args = len(arg_sorts_for_inference)
            inferred_arg_sorts = []
            valid_inference = True
            if num_args > 0:
                for arg in arg_sorts_for_inference:
                    if hasattr(arg, 'sort') and callable(arg.sort):
                        inferred_arg_sorts.append(arg.sort())
                    else:
                        print(f"    Warning: Cannot infer sort for argument of {clean_name}. Argument: {arg}. Defaulting to Item.")
                        inferred_arg_sorts.append(Item) # Default sort
                        # valid_inference = False # Có thể quyết định không tạo nếu không rõ sort
                        # break
            else: # Predicate không có đối số? Ví dụ: Raining (0-ary)
                predicate_cache[cache_key] = z3.Const(clean_name, z3.BoolSort())
                return predicate_cache[cache_key]

            # if valid_inference:
            signature = inferred_arg_sorts + [z3.BoolSort()]
            print(f"    Inferred signature: {[s.name() for s in signature[:-1]]} -> {signature[-1].name()}")
            predicate_cache[cache_key] = z3.Function(clean_name, *signature)
            # else:
            #     print(f"    Could not infer signature for {clean_name}. Skipping declaration.")
            #     return None # Hoặc raise lỗi

    # Lấy từ cache
    func = predicate_cache.get(cache_key)
    if func is None:
        # Should not happen if declaration logic above works
        raise RuntimeError(f"Failed to get or create predicate '{clean_name}' with arity {arity}.")
    # (Optional) Thêm kiểm tra arity/signature ở đây nếu cần
    # expected_arity = len(arg_sorts_for_inference)
    # if func.decl().arity() != expected_arity:
    #     print(f"  Warning: Arity mismatch for {clean_name}. Expected {expected_arity}, got {func.decl().arity()}.")

    return func


# --- 2. Hàm Parse Premises-FOL (Tổng quát hơn dùng Regex) ---
def parse_fol_string_to_z3(fol_str):
    """
    Cố gắng parse một chuỗi FOL thành biểu thức Z3 bằng regex cho các mẫu phổ biến.
    Hàm này *vẫn còn hạn chế* và cần được mở rộng/tinh chỉnh dựa trên dataset.

    Args:
        fol_str (str): Chuỗi FOL cần parse.

    Returns:
        z3.ExprRef | None: Biểu thức Z3 tương ứng hoặc None nếu không parse được.
    """
    ################   TEST #########
    # fol_str = "Q(Const) → R(Const)"

    ##################################

    # Các trường họp chưa xử lý được
    # ---------------------------------------------------------
    
    # Xóa các dấu sapce
    fol_str = fol_str.strip()

    # Nếu có dấu ngoặc tròn bọc toàn bộ thì loại bỏ
    # Ví dụ: ((A ∧ B) ∧ C) chuyển thành (A ∧ B) ∧ C
    def strip_outer_parentheses(fol_str):
        while fol_str.startswith("(") and fol_str.endswith(")"):
            depth = 0
            matched = True
            for i in range(len(fol_str)):
                if fol_str[i] == '(':
                    depth += 1
                elif fol_str[i] == ')':
                    depth -= 1
                    if depth == 0 and i != len(fol_str) - 1:
                        matched = False
                        break
            if matched:
                fol_str = fol_str[1:-1].strip()
            else:
                break
        return fol_str
    fol_str = strip_outer_parentheses(fol_str)

    # Xét trường hợp ∃x, (P(x)), lúc này fol_str = ", (P(x))"
    if fol_str.startswith(","):
        fol_str = fol_str[1:].strip()

    # Xử lý dạng ForAll và Exist trong FOL con
    # ----------------------------------------------------------------

    # Chuyển ForAll thành ∀
    match = re.fullmatch(r"ForAll\(\s*(\w+)\s*,\s*(.+)\s*\)", fol_str)
    if match:
        var = match.group(1)    # biến lượng từ, ví dụ: s
        body = match.group(2)   # phần biểu thức, ví dụ: completes_assignment(s,m) ∨ takes_exam(s,m)

        # Tạo lại biểu thức FOL
        fol_str = f"∀{var} ({body})"

    # Chuyển Exists thành ∃
    match = re.fullmatch(r"Exists\(\s*(\w+)\s*,\s*(.+)\s*\)", fol_str)
    if match:
        var = match.group(1)    # biến lượng từ, ví dụ: s
        body = match.group(2)   # phần biểu thức, ví dụ: completes_assignment(s,m) ∨ takes_exam(s,m)

        # Tạo lại biểu thức FOL
        fol_str = f"∃{var} ({body})"


    # Xử lý trường hợp ¬(Exists(x, P(x)) → Exists(x, Q(x))), đưa về dạng: ∃x P(x) ∧ ∀x ¬R(x)
    match = re.fullmatch(r"¬\(\s*Exists\(\s*(\w+)\s*,\s*(\w+)\(\1\)\s*\)\s*→\s*Exists\(\s*\1\s*,\s*(\w+)\(\1\)\s*\)\s*\)", fol_str)
    if match:
        var = match.group(1)
        p_func = match.group(2)
        r_func = match.group(3)
        fol_str =  f"∃{var} {p_func}({var}) ∧ ∀{var} ¬{r_func}({var})"


    # Xử lý trường hợp ¬Exists(x, P(x)), đưa về dạng: ∀x ¬P(x)
    def transform_negated_exists_to_forall(expression):
        pattern = r"¬\s*Exists\s*\(\s*([a-zA-Z_]\w*)\s*,\s*([a-zA-Z_]\w*)\s*\(\s*\1\s*\)\s*\)"
        return re.sub(pattern, r"∀\1 ¬\2(\1)", expression)

    # Xử lý trường hợp ¬ForAll(x, P(x)), đưa về dạng: ∃x ¬P(x)
    def transform_negated_forall_to_exists(expression):
        pattern = r"¬\s*ForAll\s*\(\s*([a-zA-Z_]\w*)\s*,\s*([a-zA-Z_]\w*)\s*\(\s*\1\s*\)\s*\)"
        return re.sub(pattern, r"∃\1 ¬\2(\1)", expression)

    fol_str = transform_negated_exists_to_forall(fol_str)
    fol_str = transform_negated_forall_to_exists(fol_str)

    # ----------------------------------------------------------------

    print(fol_str)

    # ------------------------------------------------------------------------------------
    # Mẫu: P hoặc ¬P, không đối số
    if '(' not in fol_str:
        if '¬' in fol_str:
            fol_str = fol_str[1:]
            P = get_predicate(fol_str)
            return z3.Not(P)
        else:
            P = get_predicate(fol_str)
            return P
    # ------------------------------------------------------------------------------------


    # Mẫu:
    # ¬P(const)
    # ¬P(x)
    # P(ABC)
    # P(x)
    # Q(Const, Const)
    # P(R(S(x)))
    # P(Q(S(t)))
    # P(S(a), V(b))
    # P(Q(Const, x), 3)
    # proportional(sides(ABC), sides(DEF))
    match = regex.search(r"¬*\w+\((?:[^()]+|(?R))*\)", fol_str)
    if match and not fol_str.startswith('∀') and not fol_str.startswith('∃') and fol_str == match.group():
        pred = match.group()
        pred_name, args = pred.split('(', 1)

        # Kiểm tra trường hợp P(Q(S(t)))
        if '(' in args:

            if ',' in args: # Trường hợp P(S(a), V(b))
                args = args[:-1]

                predicates = split_top_level(args, delimiter=',')

                predicates = [predicate.strip() for predicate in predicates]

                args = []

                for predicate in predicates:
                    if ('(') in predicate:
                        predicate = parse_fol_string_to_z3(predicate)
                    else:
                        predicate = z3.Const(predicate, Item)

                    args.append(predicate)
                
                P = get_predicate(pred_name, *args)
                return P(*args)
            else:
                args = args[:-1]
                # args = Q(S(t))

                sub_predicate = parse_fol_string_to_z3(args)
                P = get_predicate(pred_name, sub_predicate)

                return P(sub_predicate)
        else:
            args = args.split(')')[0]

            if ',' in args:
                args = args.split(',')
            
                args = [z3.Const(arg.strip(), Item) for arg in args]

                if '¬' in pred_name:
                    pred_name = pred_name[1:]
                    P = get_predicate(pred_name, *args)
                    return z3.Not(P(*args))
                else:
                    P = get_predicate(pred_name, *args)
                    return P(*args)
            else:
                args = z3.Const(args.strip(), Item)

                if '¬' in pred_name:
                    pred_name = pred_name[1:]
                    P = get_predicate(pred_name, args)
                    return z3.Not(P(args))
                else:
                    P = get_predicate(pred_name, args)
                    return P(args)

    # Mẫu:
    # ∃x (P(x))  
    # ∀x (P(x))
    # ∀x (P(x) → Q(x))
    # ∀x (¬P(x) → ¬Q(x))
    # ∀x ((P(x) ∧ Q(x)) → R(x))
    # ∀a((P(a) ∧ Q(R(a))) → S(a))
    # ∃x(T(x))

    if fol_str.startswith(('∀', '∃')):
        sign = fol_str[0]

        var = ""
        i = 1
        while(fol_str[i] != '∀' and fol_str[i] != '∃' and fol_str[i] != ' ' and fol_str[i] != '('):
            var += fol_str[i]
            i+=1
        var = z3.Const(var, Item)

        fol_str = fol_str[i:].strip()

        predicate = parse_fol_string_to_z3(fol_str)

        if sign == '∀':
            return z3.ForAll([var], predicate)
        elif sign == '∃':
            return z3.Exists([var], predicate)
    elif fol_str.startswith('¬(') and '→' not in fol_str:
        sign = fol_str[0]

        var = ""
        pred = fol_str[2:-1].strip()

        predicate = parse_fol_string_to_z3(pred)

        return z3.Not(predicate)
            
    
    # ∀a∀b∀c((higher(a, b) ∧ higher(b, c)) → higher(a, c))
    match = re.fullmatch(
        r"∀(\w)∀(\w)∀(\w)\s*\(\s*\((.*?)\)\s*→\s*(\w+)\((.*?)\)\s*\)", fol_str)

    if match:
        # Lấy tên biến (a, b, c) - DÒNG NÀY BỊ COMMENT TRONG CODE CỦA BẠN! CẦN BỎ COMMENT
        var1, var2, var3 = match.group(1), match.group(2), match.group(3)

        left_expr_str = match.group(4) # Chuỗi: "higher(a, b) ∧ higher(b, c)"
        right_pred_name = match.group(5) # Chuỗi: "higher"
        right_args_str = match.group(6) # Chuỗi: "a, c"
        right_args_list = [arg.strip() for arg in right_args_str.split(',')] # List: ['a', 'c']

        # Tạo biến Z3 tương ứng với kiểu Degree
        local_vars = {
            var1: z3.Const(var1, Item),
            var2: z3.Const(var2, Item),
            var3: z3.Const(var3, Item)
        }

        # Parse các predicate trong vế trái (nối bằng ∧)
        left_predicates_z3 = []
        for pred_str in left_expr_str.split("∧"):
            pred_str = pred_str.strip()
            if pred_str:
                # Parse tên hàm và đối số từ chuỗi như "higher(a, b)"
                match_pred = re.match(r"(\w+)\((.*?)\)", pred_str)
                if match_pred:
                    func_name = match_pred.group(1).strip() # "higher"
                    args_str = match_pred.group(2).strip() # "a, b"
                    arg_names = [arg.strip() for arg in args_str.split(',')] # ['a', 'b']

                    # Lấy đối tượng Z3.Const từ local_vars dựa trên tên
                    z3_args = [local_vars[name] for name in arg_names] # [local_vars['a'], local_vars['b']]

                    # Lấy hoặc tạo hàm Z3 'higher(Degree, Degree) -> Bool'
                    # CẦN đảm bảo get_predicate trả về đúng signature
                    P = get_predicate(func_name, *z3_args) # Truyền z3_args để giúp get_predicate (nếu cần)

                    # Kiểm tra xem P có đúng là hàm nhận 2 đối số Degree không (an toàn hơn)
                    left_predicates_z3.append(P(*z3_args)) # Gọi hàm Z3: P(local_vars['a'], local_vars['b'])
                else:
                     print(f"Error: Could not parse predicate structure in left expression: {pred_str}")
                     return None # Lỗi parse
            else:
                 # Xử lý trường hợp chuỗi rỗng nếu có lỗi split
                 pass


        # Xử lý vế phải
        right_args_z3 = [local_vars[name] for name in right_args_list] # [local_vars['a'], local_vars['c']]
        R = get_predicate(right_pred_name, *right_args_z3) # Lấy hàm Z3 'higher'

        # Kiểm tra signature của R
        right_expr_z3 = R(*right_args_z3) # Gọi hàm Z3: R(local_vars['a'], local_vars['c'])

        # Tạo biểu thức Z3 hoàn chỉnh: ∀a∀b∀c (AND(left_preds) → right_expr)
        # Đảm bảo truyền list các *biến Z3* vào ForAll
        quantified_vars = [local_vars[var1], local_vars[var2], local_vars[var3]]

        # Kiểm tra nếu left_predicates_z3 không rỗng
        if not left_predicates_z3:
             print(f"Error: No predicates found in the left expression: {left_expr_str}")
             return None

        return z3.ForAll(quantified_vars, z3.Implies(z3.And(*left_predicates_z3), right_expr_z3))

    

    # Mẫu : 
    #       P(Const) ∧ Q(Const)
    #       P(R(S(x)) ∧ Q(Const)) ∧ Q(Const) -> Q(Const) ∧ Q(Const) -> Q(Const)
    #       Q(Const) -> Q(Const)
    if not fol_str.startswith(('∀', '∃')):
        arrow_parts = split_top_level(fol_str, delimiter='→')
        # Nếu fol_str = "P(R(S(x)) ∧ Q(Const)) ∧ (Q(Const) → Q(Const)) ∧ Q(Const) → Q(Const)"
        # thì arrow_parts gồm:
        # P(R(S(x)) ∧ Q(Const)) ∧ (Q(Const) → Q(Const)) ∧ Q(Const)
        # Q(Const)
        # nối với nhau bằng →

        # Chuyển từng phần → thành biểu thức `∧`
        z3_parts = []
        
        print("PARTS")
        for arrow_part in arrow_parts:
            arrow_part = strip_outer_parentheses(arrow_part)
            if split_top_level(arrow_part, delimiter='∧')[0] != arrow_part.strip():
                hat_parts = split_top_level(arrow_part, delimiter='∧')
                # hat_parts gồm:
                # P(R(S(x)) ∧ Q(Const))
                # (Q(Const) → Q(Const))
                # Q(Const)
                # Q(Const)
                # nối với nhau bằng ∧

                # Tạo predicates để nối tất cả các hatparts lại với nhau
                hat_predicates = []

                for hat_part in hat_parts:
                    hat_predicates.append(parse_fol_string_to_z3(hat_part))

                # Nối các phần lại bằng z3.And nếu nhiều phần
                if len(hat_predicates) == 1:
                    z3_parts.append(hat_predicates[0])
                else:
                    print("Đã nối lại bằng mũ")
                    z3_parts.append(z3.And(*hat_predicates))

            elif split_top_level(arrow_part, delimiter='∨')[0] != arrow_part.strip():

                v_parts = split_top_level(arrow_part, delimiter='∨')

                # Tạo predicates để nối tất cả các hatparts lại với nhau
                v_predicates = []

                for v_part in v_parts:
                    v_predicates.append(parse_fol_string_to_z3(v_part))

                # Nối các phần lại bằng z3.And nếu nhiều phần
                if len(v_predicates) == 1:
                    z3_parts.append(v_predicates[0])
                else:
                    z3_parts.append(z3.Or(*v_predicates))
            else:
                def z3_parts_equivalence(preds):
                    if len(preds) == 1:
                        return preds[0]
                    expr = preds[0]
                    for next_expr in preds[1:]:
                        expr = expr == next_expr  # z3 xử lý tương đương bằng ==
                    return expr

                e_parts = split_top_level(arrow_part, delimiter='↔')

                # Tạo predicates để nối tất cả các hatparts lại với nhau
                e_predicates = []
                for e_part in e_parts:
                    e_predicates.append(parse_fol_string_to_z3(e_part))

                z3_parts.append(z3_parts_equivalence(e_predicates))


        # Nối tất cả bằng chuỗi z3.Implies
        print("Đã nối lại bằng mũi tên")
        expr = z3_parts[-1]
        for prev in reversed(z3_parts[:-1]):
            expr = z3.Implies(prev, expr)

        return expr
    
    # *** Thêm các quy tắc regex khác cho các mẫu FOL bạn tìm thấy trong dataset ***

    # Nếu không khớp mẫu nào
    print(f"Warning: Could not parse FOL string with current rules: '{fol_str}'")
    return None

# --- 4. Hàm xử lý chính ---
# def process_dataset(data):
#     """
#     Xử lý toàn bộ dataset đã được load.

#     Args:
#         data (list): Danh sách các record từ file JSON.

#     Returns:
#         list: Danh sách các record đã được xử lý, bổ sung thông tin Z3.
#     """
#     processed_records = []
#     premise_parse_errors = 0
#     total_premises = 0
#     total_questions = 0

#     for i, record in enumerate(data):
#         print(f"\n--- Processing Record {i} ---")
#         processed_record = {
#             # 'original_index': record.get('id_sample'),
#             'premises_nl': record.get('premises-NL', []),
#             # 'premises_fol_str': record.get('premises-FOL', []),
#             'questions_nl': record.get('questions', []),
#             # 'answers_gt': record.get('answers', []), # Ground Truth
#             # 'idx_gt': record.get('idx', []),
#             # 'explanation_gt': record.get('explanation', []),
#             'z3_premises': [],
#             'parsed_questions': []
#         }

#         # Parse Premises
#         current_premise_errors = 0
#         for idx, fol_str in enumerate(processed_record['premises_fol_str']):
#             total_premises += 1
#             z3_premise = parse_fol_string_to_z3(fol_str)
#             if z3_premise is not None:
#                 # Lưu cả biểu thức Z3 và chỉ số gốc (0-based)
#                 processed_record['z3_premises'].append({'expr': z3_premise, 'original_index': idx})
#             else:
#                 premise_parse_errors += 1
#                 current_premise_errors += 1
        
#         for question_str in processed_record['questions_nl']:
#             z3_question = parse_fol_string_to_z3(question_str)
#             if z3_question is not None:
#                 # Lưu cả câu hỏi Z3
#                 processed_record['parsed_questions'].append({'ques': z3_question})
#             else:
#                 print("Question Parse Error")

#         if current_premise_errors > 0:
#              print(f"Record {i}: Encountered {current_premise_errors} premise parsing errors.")

#         processed_records.append(processed_record)

#     print("\n--- Processing Summary ---")
#     print(f"Total records processed: {len(data)}")
#     print(f"Total premises encountered: {total_premises}")
#     print(f"Premise parsing errors: {premise_parse_errors} ({premise_parse_errors/total_premises:.2%} errors)")
#     print(f"Total questions encountered: {total_questions}")
#     print(f"Total unique predicates identified: {len(predicate_cache)}")
#     print("Identified predicates:", list(predicate_cache.keys()))


#     return processed_records

# --- Chạy chương trình ---
# if __name__ == "__main__":
    # !!! THAY ĐỔI ĐƯỜNG DẪN NÀY !!!
    # dataset_filepath = r'datasets/train.json' # Hoặc đường dẫn đầy đủ

#     item = {
#     "premises-NL": [
#         "If a Python code is well-tested, then the project is optimized.",
#         "If a Python code does not follow PEP 8 standards, then it is not well-tested.",
#         "All Python projects are easy to maintain.",
#         "All Python code is well-tested.",
#         "If a Python code follows PEP 8 standards, then it is easy to maintain.",
#         "There exists at least one Python project that has clean and readable code.",
#         "If a Python code is well-tested, then it follows PEP 8 standards.",
#         "If a Python project is not optimized, then it is not well-tested.",
#         "There exists at least one Python project that is well-structured.",
#         "If a Python project is well-structured, then it is optimized.",
#         "If being well-tested implies following PEP 8 standards, then all Python code is well-tested.",
#         "If being well-structured implies optimization, then if a Python project is not optimized, it is not welltested.",
#         "If a Python project is easy to maintain, then it is well-tested.",
#         "If a Python project is optimized, then it has clean and readable code.",
#         "All Python projects are well-structured.",
#         "All Python projects have clean and readable code.",
#         "There exists at least one Python project that follows best practices.",
#         "There exists at least one Python project that is optimized.",
#         "If a Python project is not well-structured, then it does not follow PEP 8 standards."
#     ],
#     "questions": [
#         "Based on the above premises, which conclusion is correct?\nA. If a Python project is not optimized, then it is not well-tested.\nB. If all Python projects are optimized, then all Python projects are wellstructured.\nC. If a Python project is well-tested, then it must be clean and readable.\nD. If a Python project is not optimized, then it does not follow PEP 8 standards.",
#         "According to the above premises, is the following statement true?\nStatement: If all Python projects are well-structured, then all Python projects are optimized."
#     ]
# }

    # Load data
    raw_data = load_json_dataset(dataset_filepath)

    if raw_data and isinstance(raw_data, list):
        # Process data
        processed_data = process_dataset(raw_data)

        # In ra thông tin xử lý của record đầu tiên để kiểm tra
        if processed_data:
            print("\n--- Sample Processed Record (Index 0) ---")
            first_record = processed_data[0]
            print(first_record)

            # print("Original FOL Strings:", first_record['premises_fol_str'])
            # print("Parsed Z3 Premises:", [(p['expr'], p['original_index']) for p in first_record['z3_premises']])
            # print("\nOriginal Questions:", first_record['questions_nl'])
            # print("Parsed Questions:")
            # for pq in first_record['parsed_questions']:
            #     print(f"  Type: {pq['type']}")
            #     print(f"  Goal/Data: {pq['goal_data']}") # In ra cấu trúc goal đã parse
            #     print("-" * 10)

            print("---------------RESULT---------------")

            result_counts = Counter()

            solver = z3.Solver()

            # Gắn label cho từng premise
            labels = []
            num_premises = len(first_record['z3_premises'])
            for i, item in enumerate(reversed(first_record['z3_premises'])):
                label = z3.Bool(f"p{num_premises-i}")  # gán tên giả định
                solver.assert_and_track(item['expr'], label)
                labels.append(label)

            # for i, item in enumerate(first_record['z3_premises']):
            #     label = z3.Bool(f"p{i+1}")  # gán tên giả định
            #     solver.assert_and_track(item['expr'], label)
            #     labels.append(label)

                solver.push()
                solver.add(z3.Not(first_record['parsed_questions'][0]['ques']))
                result = solver.check()

                # In kết quả
                if result == z3.unsat:
                    result_counts["YES"] += 1
                    used = solver.unsat_core()  # trả về danh sách các label đã dùng
                    print("Các giả định đã dùng:", used)
                    # Lấy chỉ số index tương ứng từ tên p0, p1, ...
                    used_indices = [int(str(label)[1:]) for label in used]
                    print("Vị trí trong premises_fol_str:", used_indices)
                    print("----")
                    for idx in used_indices:
                        print(first_record['z3_premises'][idx-1])
                elif result == z3.sat:
                    result_counts["NO"] += 1
                else:
                    # print("UNKNOW: Sophia does not qualify for the scholarship.")
                    result_counts["UNKNOWN"] += 1
                solver.pop()

            print("\nKết quả tổng hợp:", dict(result_counts))
            print("Kết quả xảy ra nhiều nhất:", result_counts.most_common(1)[0])




    elif raw_data:
        print("Error: Expected dataset to be a JSON list of records.")
    else:
        print("Failed to load dataset.")
    log_file.close()


def parse_nl_to_FOL(premises_nl):
    return "∀x (WT(x) → O(x))"


@app.route("/query", methods=["POST"])
@limiter.limit("10 per second")  # extra layer if you want per-route
def query():
    auth_header = request.headers.get("Authorization")
    if not auth_header or not auth_header.startswith("Bearer ") or auth_header.split(" ")[1] != API_KEY:
        return jsonify({"error": "Unauthorized"}), 401

    data = request.json
    premises_nl = data.get("premises-NL", [])
    questions_nl = data.get("questions", [])
    
    answers = []
    z3_premises = []
    idx = []
    explanations = []
    premises_FOL = []
    questions_FOL = []


    for premise_NL in premises_nl:
        premises_FOL.append(parse_nl_to_FOL(premise_NL))  # Model
    # premises_FOL = [
    #     "∀x (WT(x) → O(x))",
    #     "∀x (¬PEP8(x) → ¬WT(x))",
    #     "∀x (EM(x))",
    #     "∀x (WT(x))",
    # ]
    
    for premise in premises_FOL:
        z3_premises.append(parse_fol_string_to_z3(premise))
    
    for question_nl in questions_nl:
        questions_FOL.append(parse_nl_to_FOL(question_nl))  # Model


    for q in questions_FOL:
        z3_question = parse_fol_string_to_z3(q)

        result_counts = Counter()

        solver = z3.Solver()

        # Gắn label cho từng premise
        labels = []
        num_premises = len(z3_premises)
        for i, item in enumerate(reversed(z3_premises)):
            label = z3.Bool(f"p{num_premises-i}")  # gán tên giả định
            solver.assert_and_track(item, label)
            labels.append(label)

        # for i, item in enumerate(first_record['z3_premises']):
        #     label = z3.Bool(f"p{i+1}")  # gán tên giả định
        #     solver.assert_and_track(item['expr'], label)
        #     labels.append(label)

            solver.push()
            solver.add(z3.Not(z3_question))
            result = solver.check()

            # In kết quả
            if result == z3.unsat:
                result_counts["YES"] += 1
                used = solver.unsat_core()  # trả về danh sách các label đã dùng
                print("Các giả định đã dùng:", used)
                # Lấy chỉ số index tương ứng từ tên p0, p1, ...
                used_indices = [int(str(label)[1:]) for label in used]
                print("Vị trí trong premises_fol_str:", used_indices)
                print("----")
                for idx in used_indices:
                    print(z3_premises[idx-1])
            elif result == z3.sat:
                result_counts["NO"] += 1
            else:
                # print("UNKNOW: Sophia does not qualify for the scholarship.")
                result_counts["UNKNOWN"] += 1
            solver.pop()

        print("\nKết quả tổng hợp:", dict(result_counts))
        print("Kết quả xảy ra nhiều nhất:", result_counts.most_common(1)[0])
    
    return jsonify({
        "answers": [
            "A",
            "Yes"
        ],
        "idx": [
            [
                1
            ],
            [
                7,
                10
            ]
        ],
        "explanation":  [
            "Premise 1 states that if a Python project is well-tested, it is optimized. By logical contraposition, if a project is not optimized, it is not well-tested, supporting option A with the fewest premises. Option B is false because optimization does not imply well-structured projects. Option C follows from premises 4, 1, and 9 but requires more steps. Option D follows from premises 1 and 6 but is less direct than A.",
            "Premise 10 confirms all Python projects are well-structured. Premise 7 states that well-structured projects are optimized, implying all projects are optimized, so the statement that well-structured projects imply optimized projects holds."
        ]
    })


if __name__ == "__main__":
    print("PORT:", PORT)
    app.run(host="0.0.0.0", port=PORT)

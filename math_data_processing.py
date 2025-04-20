import json
import z3
import re
import os
from collections import defaultdict
import sys
from test_parts_split import split_top_level
import regex


# Redirect stdout và stderr
log_file = open('math_logs.txt', 'w', encoding='utf-8')
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
    ('angle', 1): (Item, z3.RealSort()),
    ('safety_test', 1): (Item, z3.BoolSort()),
    ('safety_test', 3): (Item, Item, Item, z3.BoolSort()),
    ('find_replacement', 1): (Item, z3.BoolSort()),
    ('EnglishResultDate', 1): (Item, z3.StringSort())
}

def get_predicate(name, *arg_sorts_for_inference, return_sort=z3.BoolSort()):
    """
    Lấy hoặc tạo predicate Z3. Ưu tiên signature định nghĩa trước.
    Nếu không có, thử suy luận signature dựa trên sort của đối số mẫu được truyền vào.
    """
    print(name)
    print("PREDICATE_OK")
    clean_name = name.strip()
    if not clean_name:
        raise ValueError("Predicate name cannot be empty")
    
    arity = len(arg_sorts_for_inference)
    cache_key = (clean_name, arity)

    if cache_key not in predicate_cache:
        print(f"  Defining Predicate: {clean_name} with arity {arity}")

        if cache_key in PREDEFINED_SIGNATURES:
            sig = PREDEFINED_SIGNATURES[cache_key]
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
                predicate_cache[cache_key] = z3.Const(clean_name, return_sort)
                return predicate_cache[cache_key]

            # if valid_inference:
            signature = inferred_arg_sorts + [return_sort]
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
def parse_fol_string_to_z3(fol_str, return_sort=z3.BoolSort()):
    """
    Cố gắng parse một chuỗi FOL thành biểu thức Z3 bằng regex cho các mẫu phổ biến.
    Hàm này *vẫn còn hạn chế* và cần được mở rộng/tinh chỉnh dựa trên dataset.

    Args:
        fol_str (str): Chuỗi FOL cần parse.

    Returns:
        z3.ExprRef | None: Biểu thức Z3 tương ứng hoặc None nếu không parse được.
    """
    ################   TEST #########
    # fol_str = "academic_warning(x) ∧ next_term_gpa(x) > 6.5 ∧ ¬violation(x) → lift_warning(x)"

    ##################################

    # Các trường họp chưa xử lý được
    # ---------------------------------------------------------

    if "SubmittedApplication" in fol_str:
        print(f"Warning: Could not parse FOL string with current rules: '{fol_str}'")
        return None
    
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
    # ¬P(const) = const
    # ¬P(x) = const
    # P(ABC)
    # P(x)
    # Q(Const, Const)
    # P(R(S(x)))
    # P(Q(S(t)))
    # P(S(a), V(b))
    # P(Q(Const, x), 3)
    # proportional(sides(ABC), sides(DEF))

    # match = regex.search(r"¬*\w+\((?:[^()]+|(?R))*\)\s*=+\s*\w+", fol_str)
    # match = regex.search(r"¬*\w+\((?:[^()]+|(?R))*\)\s*(=|≥|>|<|≠|≤|∈)\s*\w+\.*\w*", fol_str)
    pattern = r'''
^
\s*
(?P<lhs>
    \w+\([^()]+\)                     # hàm đơn hoặc với đối số, ví dụ: GPAUse(c)
    (?:\s*[\+\-]\s*\w+\([^()]+\))*    # cộng/trừ với các hàm khác (nếu có)
)
\s*(?P<op>=|≥|>|<|≠|≤|∈)\s*
(?P<rhs>
    \w+\(
        (?:
            [^()]+                    # đối số không có ngoặc
            |
            \w+\([^()]+\)             # hỗ trợ một lớp lồng nhau như Max(Grades(c))
        )
    \)
    (?:\s*[\+\-]\s*\w+\([^()]+\))*    # cộng/trừ tiếp (nếu có)
    |
    \d+(?:/\d+){0,2}
    |
    \d+(?:\.\d+)?
    |
    \w+
)
\s*$
'''
    match = re.search(pattern, fol_str, re.VERBOSE)
    # membership_duration(Alex) = 8
    if match and not fol_str.startswith('∀') and not fol_str.startswith('∃') and fol_str == match.group():
        pred = match.group("lhs")
        operator = match.group("op")

        value_return = match.group("rhs").strip()

        def smart_parse_value(value_return):
            try:
                if '(' in value_return and ')' in value_return:
                    # Là một biểu thức hàm, ví dụ: Max(Grades(c)) → parse sau bằng parse_fol_string_to_z3
                    return parse_fol_string_to_z3(value_return, return_sort=z3.RealSort())
                elif '.' in value_return:  # dấu chấm cho biết đây là số thực
                    return z3.RealVal(float(value_return))
                else:
                    return z3.IntVal(int(value_return))
            except ValueError:
                return z3.StringVal(value_return)

        value_return = smart_parse_value(value_return)
        
        z = parse_fol_string_to_z3(pred, return_sort = z3.RealSort())

        if operator == "=":
            z_function = z == value_return
        elif operator == "≠":
            z_function = z != value_return
        elif operator == ">":
            z_function = z > value_return
        elif operator == "<":
            z_function = z < value_return
        elif operator == "≥":
            z_function = z >= value_return
        elif operator == "≤":
            z_function = z <= value_return
        elif operator == "+":
            z_function = z + value_return
        elif operator == "*":
            z_function = z * value_return
        # elif operator == ".":
        #     z_function = z * value_return  # giả định dùng như nhân chấm, có thể tùy bạn sửa
        elif operator == "∈":
            # ⚠️ Cần kiểm tra z và value_return là kiểu gì
            # Nếu value_return là một tập hợp:
            z_function = z3.IsMember(z, value_return)
        return z_function
    
    # ------------------------------------------------------------------------------------

    # angle(A) + angle(B) + angle(C) = 180
    # match = re.match(r'(\w+)\((\w)\)(\s*[\+\-]\s*(\w+)\((\w)\))*\s*=\s*([\w\.]+)', fol_str)
    pattern = r'''^
\s*
(?P<lhs>
    \w+\([^\(\)]+\)                     # hàm có 1 hoặc nhiều đối số
    (?:\s*[\+\-]\s*\w+\([^\(\)]+\))*    # nhiều hàm cộng/trừ nhau
)
\s*(?P<op>=|≥|>|<|≠|≤|∈)\s*
(?P<rhs>
    (?:
        \w+\([^\(\)]+\)                 # hàm có 1 hoặc nhiều đối số
        (?:\s*[\+\-]\s*\w+\([^\(\)]+\))*  # nhiều hàm cộng/trừ nhau
    )
    |
    (?:
        \d+(?:\.\d+)?                   # số thực hoặc nguyên
    )
    |
    \w+                                 # biến đơn
)
\s*$
'''
    match = re.match(pattern, fol_str, re.VERBOSE)
    if match:
        # operator = match.group("op")
        # left_predicates, right_predicates = fol_str.split(operator, 1)

        # left_predicates = left_predicates.strip()
        # right_predicates = right_predicates.strip()

        # left_predicates = left_predicates.split("+")
        # left_predicates = [left_predicate.strip() for left_predicate in left_predicates]

        # list_predicates = []

        # for left_predicate in left_predicates:
        #     list_predicates.append(parse_fol_string_to_z3(left_predicate, return_sort=z3.RealSort()))

        
        # left_z = z3.Sum(list_predicates)

        # if '(' in right_predicates:
        #     right_predicates = right_predicates.split("+")
        #     right_predicates = [right_predicate.strip() for right_predicate in right_predicates]

        #     list_predicates = []

        #     for right_predicate in right_predicates:
        #         list_predicates.append(parse_fol_string_to_z3(right_predicate, return_sort=z3.RealSort()))
            
        #     right_z = z3.Sum(list_predicates)

        #     if operator == "=":
        #         return left_z == right_z
        #     elif operator == "<":
        #         return left_z < right_z
        # else:
        #     value =  z3.RealVal(float(right_predicates))
        #     if operator == "=":
        #         return left_z == value
        #     elif operator == "<":
        #         return left_z < value

        operator = match.group("op")
        lhs_str = match.group("lhs").strip()
        rhs_str = match.group("rhs").strip()

        def parse_side(expr):
            parts = re.findall(r'[+-]?\s*[^+-]+', expr)
            result = []
            for part in parts:
                part = part.strip()
                if part.startswith('-'):
                    result.append(-parse_fol_string_to_z3(part[1:].strip(), return_sort=z3.RealSort()))
                elif part.startswith('+'):
                    result.append(parse_fol_string_to_z3(part[1:].strip(), return_sort=z3.RealSort()))
                else:
                    result.append(parse_fol_string_to_z3(part.strip(), return_sort=z3.RealSort()))
            return z3.Sum(result) if len(result) > 1 else result[0]

        left_z = parse_side(lhs_str)

        if '(' in rhs_str:
            right_z = parse_side(rhs_str)
        else:
            try:
                right_z = z3.RealVal(float(rhs_str))
            except ValueError:
                right_z = parse_fol_string_to_z3(rhs_str, return_sort=z3.RealSort())

        # Trả về biểu thức so sánh Z3 tương ứng
        if operator == "=":
            return left_z == right_z
        elif operator == "<":
            return left_z < right_z
        elif operator == ">":
            return left_z > right_z
        elif operator == "≥":
            return left_z >= right_z
        elif operator == "≤":
            return left_z <= right_z
        elif operator == "≠":
            return left_z != right_z
        elif operator == "∈":
            # Tùy trường hợp bạn xử lý riêng (ví dụ `x ∈ A`)
            raise NotImplementedError("Chưa xử lý toán tử ∈.")
        else:
            raise ValueError("Toán tử không hợp lệ.")
        


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
                
                P = get_predicate(pred_name, *args, return_sort = return_sort)
                return P(*args)
            else:
                args = args[:-1]
                # args = Q(S(t))

                sub_predicate = parse_fol_string_to_z3(args)
                P = get_predicate(pred_name, sub_predicate, return_sort = return_sort)

                return P(sub_predicate)
        else:
            args = args.split(')')[0]

            if ',' in args:
                args = args.split(',')
            
                args = [z3.Const(arg.strip(), Item) for arg in args]

                if '¬' in pred_name:
                    pred_name = pred_name[1:]
                    P = get_predicate(pred_name, *args, return_sort = return_sort)
                    return z3.Not(P(*args))
                else:
                    P = get_predicate(pred_name, *args, return_sort = return_sort)
                    return P(*args)
            else:
                args = z3.Const(args.strip(), Item)

                if '¬' in pred_name:
                    pred_name = pred_name[1:]
                    P = get_predicate(pred_name, args, return_sort = return_sort)
                    return z3.Not(P(args))
                else:
                    P = get_predicate(pred_name, args, return_sort = return_sort)
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
                    P = get_predicate(func_name, *z3_args, return_sort = return_sort) # Truyền z3_args để giúp get_predicate (nếu cần)

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
        R = get_predicate(right_pred_name, *right_args_z3, return_sort = return_sort) # Lấy hàm Z3 'higher'

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
        expr = z3_parts[-1]
        for prev in reversed(z3_parts[:-1]):
            expr = z3.Implies(prev, expr)

        return expr
    
    # ------------------------------------------------------------------------------------        
    # Mẫu: ∀x(P(x) → (∃d, Q(x, d) ∧ R(d, Const)))
    match = re.fullmatch(r"∀(\w)\s*\(\s*(\w+\(\w+\))\s*→\s*\(\s*∃(\w),\s*(.*?)\s*\)\s*\)", fol_str)
    if match:
        arg1 = match.group(1)
        func1 = match.group(2).split('(')[0]


        arg1 = z3.Const(arg1, Item)
        P = get_predicate(func1, arg1, return_sort = return_sort)
        left_func = get_predicate(func1, arg1, return_sort = return_sort)
        left_pred = left_func(arg1)


        arg2 = match.group(3)
        right_part = match.group(4)

        rhs_predicates = []
        for pred in right_part.split("∧"):
            pred = pred.strip()
            if pred:
                func_name, args_str = pred.split("(")
                args = args_str.rstrip(")").split(",")
                args = [arg.strip() for arg in args]  # ví dụ: ['x', 'd']

                args[0] = z3.Const(args[0], Item)
                args[1] = z3.Const(args[1], Item)

                R = get_predicate(func_name, args[0], args[1], return_sort = return_sort)
                rhs_predicates.append(R(args[0], args[1]))
    
        arg2 = z3.Const(arg2, Item)
        # Tạo biểu thức tồn tại (∃)
        exists_expr = z3.Exists(arg2, z3.And(*rhs_predicates))

        # Toàn bộ biểu thức
        return z3.ForAll(arg1, z3.Implies(left_pred, exists_expr))

    # *** Thêm các quy tắc regex khác cho các mẫu FOL bạn tìm thấy trong dataset ***

    # Nếu không khớp mẫu nào
    print(f"Warning: Could not parse FOL string with current rules: '{fol_str}'")
    return None

# --- 3. Hàm Parse Questions (Vẫn cần cải thiện nhiều) ---
def parse_nl_question_to_z3_goal(question_str):
    """
    Cố gắng parse câu hỏi NL thành Z3 goal(s). Cần tùy chỉnh nhiều dựa trên dataset.

    Returns:
        (object, str): Tuple chứa (Z3 goal(s) hoặc dữ liệu liên quan, question_type)
                       hoặc (None, "unknown")
    """
    local_x = z3.Const('x', Item) # Biến cục bộ

    # --- Logic nhận dạng loại câu hỏi và trích xuất thông tin ---
    # (Đây là phần phác thảo, cần logic thực tế dựa trên dataset)

    # Loại 1: Yes/No (ví dụ: "Does it follow that...")
    if "Does it follow that" in question_str and "according to the premises" in question_str:
        # Cố gắng trích xuất mệnh đề logic bên trong
        # Ví dụ rất đơn giản: tìm "if ... then ..."
        match_if_then = re.search(r"if all .* are (.*), then all .* are (.*)", question_str, re.IGNORECASE)
        if match_if_then:
            try:
                antecedent_pred_name = match_if_then.group(1).strip().split()[0] # Heuristic!
                consequent_pred_name = match_if_then.group(2).strip().split()[0] # Heuristic!
                P = get_predicate(antecedent_pred_name.upper()) # Chuẩn hóa tên
                Q = get_predicate(consequent_pred_name.upper()) # Chuẩn hóa tên
                goal = z3.ForAll([local_x], z3.Implies(P(local_x), Q(local_x)))
                return goal, "yes_no"
            except Exception as e:
                print(f"Error parsing Yes/No statement logic: {e} in question: {question_str}")
                return None, "unknown"
        else:
             # Thử các mẫu Yes/No khác
             pass

    # Loại 2: Multiple Choice (ví dụ: "Which conclusion follows...")
    elif "Which conclusion follows" in question_str and "\nA." in question_str:
        # Trích xuất các options (A, B, C, D)
        options = {}
        # Regex đơn giản để lấy text của từng option (cần kiểm tra kỹ)
        matches = re.findall(r"\n([A-D])\.\s*(.*?)(?=\n[A-D]\.|\Z)", question_str, re.DOTALL)
        parsed_options = []
        for label, text in matches:
            text = text.strip()
            # Cố gắng parse text của option thành Z3 (lại là phần khó)
            # Ví dụ: "If a ... is not optimized, then it is not well-tested"
            match_opt = re.match(r"If a .* is not (\w+), then it is not (\w+)", text, re.IGNORECASE)
            if match_opt:
                try:
                    P_name = match_opt.group(1).upper()
                    Q_name = match_opt.group(2).upper()
                    P = get_predicate(P_name)
                    Q = get_predicate(Q_name)
                    goal = z3.ForAll([local_x], z3.Implies(z3.Not(P(local_x)), z3.Not(Q(local_x))))
                    parsed_options.append({'label': label, 'text': text, 'goal': goal})
                except Exception as e:
                    print(f"Error parsing MCQ option logic: {e} in option: {text}")
                    parsed_options.append({'label': label, 'text': text, 'goal': None})
            else:
                # Thử các mẫu option khác
                parsed_options.append({'label': label, 'text': text, 'goal': None})
                print(f"Warning: Could not parse MCQ option text: {text}")

        if parsed_options:
            return parsed_options, "multiple_choice"
        else:
            return None, "unknown" # Không trích xuất được option nào

    # *** Thêm logic cho các loại câu hỏi khác (Listing, How Many) ***

    # Nếu không nhận dạng được loại câu hỏi
    print(f"Warning: Could not determine question type or parse: {question_str[:100]}...")
    return None, "unknown"

# --- 4. Hàm xử lý chính ---
def process_dataset(data):
    """
    Xử lý toàn bộ dataset đã được load.

    Args:
        data (list): Danh sách các record từ file JSON.

    Returns:
        list: Danh sách các record đã được xử lý, bổ sung thông tin Z3.
    """
    processed_records = []
    premise_parse_errors = 0
    question_parse_errors = 0
    total_premises = 0
    total_questions = 0

    for i, record in enumerate(data):
        print(f"\n--- Processing Record {i} ---")
        processed_record = {
            'original_index': i,
            'premises_nl': record.get('premises-NL', []),
            'premises_fol_str': record.get('premises-FOL', []),
            'questions_nl': record.get('questions', []),
            'answers_gt': record.get('answers', []), # Ground Truth
            'idx_gt': record.get('idx', []),
            'explanation_gt': record.get('explanation', []),
            'z3_premises': [],
            'parsed_questions': []
        }

        # Parse Premises
        current_premise_errors = 0
        for idx, fol_str in enumerate(processed_record['premises_fol_str']):
            total_premises += 1
            z3_premise = parse_fol_string_to_z3(fol_str)
            if z3_premise is not None:
                # Lưu cả biểu thức Z3 và chỉ số gốc (0-based)
                processed_record['z3_premises'].append({'expr': z3_premise, 'original_index': idx})
            else:
                premise_parse_errors += 1
                current_premise_errors += 1
        if current_premise_errors > 0:
             print(f"Record {i}: Encountered {current_premise_errors} premise parsing errors.")

        # Parse Questions
        # current_question_errors = 0
        # for q_str in processed_record['questions_nl']:
        #     total_questions += 1
        #     parsed_goal, q_type = parse_nl_question_to_z3_goal(q_str)
        #     if parsed_goal is not None:
        #          processed_record['parsed_questions'].append({
        #              'original_question': q_str,
        #              'goal_data': parsed_goal, # Can be a single goal or list of options
        #              'type': q_type
        #          })
        #     else:
        #         question_parse_errors += 1
        #         current_question_errors += 1
        # if current_question_errors > 0:
        #      print(f"Record {i}: Encountered {current_question_errors} question parsing errors.")

        # processed_records.append(processed_record)

    print("\n--- Processing Summary ---")
    print(f"Total records processed: {len(data)}")
    print(f"Total premises encountered: {total_premises}")
    print(f"Premise parsing errors: {premise_parse_errors} ({premise_parse_errors/total_premises:.2%} errors)")
    print(f"Total questions encountered: {total_questions}")
    # print(f"Question parsing errors: {question_parse_errors} ({question_parse_errors/total_questions:.2%} errors)")
    print(f"Total unique predicates identified: {len(predicate_cache)}")
    print("Identified predicates:", list(predicate_cache.keys()))


    return processed_records

# --- Chạy chương trình ---
if __name__ == "__main__":
    # !!! THAY ĐỔI ĐƯỜNG DẪN NÀY !!!
    dataset_filepath = r'datasets/math_dataset.json' # Hoặc đường dẫn đầy đủ


    # Load data
    raw_data = load_json_dataset(dataset_filepath)

    if raw_data and isinstance(raw_data, list):
        # Process data
        processed_data = process_dataset(raw_data)

        # In ra thông tin xử lý của record đầu tiên để kiểm tra
        if processed_data:
            print("\n--- Sample Processed Record (Index 0) ---")
            first_record = processed_data[0]
            print("Original FOL Strings:", first_record['premises_fol_str'])
            print("Parsed Z3 Premises:", [(p['expr'], p['original_index']) for p in first_record['z3_premises']])
            print("\nOriginal Questions:", first_record['questions_nl'])
            print("Parsed Questions:")
            for pq in first_record['parsed_questions']:
                print(f"  Type: {pq['type']}")
                print(f"  Goal/Data: {pq['goal_data']}") # In ra cấu trúc goal đã parse
                print("-" * 10)


    elif raw_data:
        print("Error: Expected dataset to be a JSON list of records.")
    else:
        print("Failed to load dataset.")
    log_file.close()

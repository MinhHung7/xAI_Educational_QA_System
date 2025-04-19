import json

def convert_arrow_in_train_json(file_path):
    # Đọc nội dung JSON dạng string
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()

    # Thay thế "->" bằng "→" trong toàn bộ nội dung
    updated_content = content.replace("->", "→")

    # Ghi lại nội dung đã thay thế vào file
    with open(file_path, 'w', encoding='utf-8') as f:
        f.write(updated_content)

    print(f"Đã thay thế '->' bằng '→' trong {file_path}")

convert_arrow_in_train_json(r"datasets/train.json")

import json
import re

def convert_fol_syntax(expr):
    """
    Chuyển chuỗi ForAll(...) hoặc Exists(...) sang ∀... hoặc ∃...
    Ví dụ: ForAll(x, ForAll(d, P(x,d))) → ∀x∀d(P(x,d))
    """

    # Thay tất cả dấu nháy đơn bằng khoảng trắng
    expr = expr.replace("'", "")
    # Thay tất cả chữ implies bằng →
    expr = expr.replace("implies", "→")
    # Thay tất cả chữ not bằng ¬
    expr = expr.replace("not ", "¬")
    # Thay tất cả ~ bằng ¬
    expr = expr.replace("~", "¬")
    # Thay tất cả & bằng ∧
    expr = expr.replace("&", "∧")
    # Thay tất cả "):" bằng ")↔"
    expr = expr.replace("):", ")↔")
    # Thay tất cả "):" bằng ")↔"
    expr = expr.replace(")↔", ",")
    # Thay tất cả "Hà" bằng "Ha"
    expr = expr.replace("Hà", "Ha")
    # Thay tất cả "GPA4.0" bằng "GPA4"
    expr = expr.replace("GPA4.0", "GPA4")
    # Thay tất cả "<=" bằng "≤"
    expr = expr.replace("<=", "≤") 
    # Thay tất cả ">=" bằng "≥"
    expr = expr.replace(">=", "≥") 
    # Thay tất cả "FORALL" bằng "ForAll"
    expr = expr.replace("FORALL", "ForAll") 
    # Thay tất cả "EXISTS" bằng "Exists"
    expr = expr.replace("EXISTS", "Exists")

    quantifier_map = {
        'ForAll': '∀',
        'Exists': '∃'
    }

    pattern = r'(ForAll|Exists)\((\w+),\s*(.*)\)$'
    variables = []
    while True:
        match = re.match(pattern, expr)
        if match:
            print(match)
            quantifier, var, inner = match.groups()
            variables.append(quantifier_map[quantifier] + var)
            expr = inner.strip()
        else:
            break
    # Chỉ đệ quy nếu phần còn lại cũng là ForAll(...) hoặc Exists(...) ở đầu chuỗi
    if re.match(pattern, expr):
        expr = convert_fol_syntax(expr)

    ans = ''.join(variables) + f'({expr})'
    return ans

# Đọc dữ liệu từ file train.json
with open(r'datasets/math_dataset.json', 'r', encoding='utf-8') as f:
    data = json.load(f)

# Chuyển đổi tất cả biểu thức trong premises-FOL
for item in data:
    if "premises-FOL" in item:
        item["premises-FOL"] = [convert_fol_syntax(expr) for expr in item["premises-FOL"]]
    elif "premise-FOL" in item:
        item["premise-FOL"] = [convert_fol_syntax(expr) for expr in item["premise-FOL"]]
    elif "premises_fol" in item:
        item["premises_fol"] = [convert_fol_syntax(expr) for expr in item["premises_fol"]]
# Ghi lại vào file train.json
with open(r'datasets/math_dataset.json', 'w', encoding='utf-8') as f:
    json.dump(data, f, ensure_ascii=False, indent=4)

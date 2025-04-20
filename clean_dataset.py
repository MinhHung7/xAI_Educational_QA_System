# File này chỉ được thao clean file train.json

import json
import re


def has_extra_closing_parenthesis(s):
    count = 0
    for char in s:
        if char == '(':
            count += 1
        elif char == ')':
            count -= 1
        # Nếu tại bất kỳ thời điểm nào count < 0 => dư dấu ')'
        # Nếu tại bất kỳ thời điểm nào count > 0 => thiếu dấu ')'
    
    return count

def convert_fol_syntax(expr):
    """
    Chuyển chuỗi ForAll(...) hoặc Exists(...) sang ∀... hoặc ∃...
    Ví dụ: ForAll(x, ForAll(d, P(x,d))) → ∀x∀d(P(x,d))
    """
    # Thay tất cả dấu mũi tên bằng mũi tên
    expr = expr.replace("->", "→")
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

    result = ''
    while expr.startswith('ForAll') or expr.startswith('Exists'):
        # Lấy loại định lượng và kí hiệu
        if expr.startswith('ForAll'):
            quant = 'ForAll'
        else:
            quant = 'Exists'
        symbol = quantifier_map[quant]

        # Tìm vị trí mở và đóng ngoặc ngoài cùng đầu tiên
        start = expr.find('(')
        count = 1
        i = start + 1
        while i < len(expr):
            if expr[i] == '(':
                count += 1
            elif expr[i] == ')':
                count -= 1
                if count == 0:
                    break
            i += 1

        # Lấy phần nội dung bên trong ForAll(...)
        inside = expr[start + 1:i]
        # Tách phần biến và phần biểu thức
        comma_index = inside.find(',')
        var_part = inside[:comma_index].strip()
        expr = inside[comma_index + 1:].strip()  # cập nhật expr cho vòng lặp tiếp theo

        # Nối các biến với kí hiệu định lượng
        variables = [v.strip() for v in var_part.split(',')]
        result += ''.join([symbol + v for v in variables])

        # Cập nhật expr từ ngoài dấu ngoặc
        expr = expr.strip()
        if expr.startswith('(') and expr.endswith(')'):
            expr = expr[1:-1].strip()

    result = result + f'({expr})'

    while has_extra_closing_parenthesis(result) != 0:
        count = has_extra_closing_parenthesis(result)

        if count < 0:
            result = result[:-1]
        elif count > 0:
            result = result + ')'

    return result


    # # pattern = r'(ForAll|Exists)\((\w+),\s*(.*)\)$'
    # pattern = r'^(ForAll|Exists)\(([^)]+)\):?\s*(.+)$'
    # variables = []
    # while True:
    #     match = re.match(pattern, expr)
    #     if match:
    #         print(match)
    #         quantifier, var, inner = match.groups()
    #         variables.append(quantifier_map[quantifier] + var)
    #         expr = inner.strip()
    #     else:
    #         break
    # # Chỉ đệ quy nếu phần còn lại cũng là ForAll(...) hoặc Exists(...) ở đầu chuỗi
    # if re.match(pattern, expr):
    #     expr = convert_fol_syntax(expr)

    # ans = ''.join(variables) + f'({expr})'
    # return ans

# Đọc dữ liệu từ file train.json
with open(r'datasets/train.json', 'r', encoding='utf-8') as f:
    data = json.load(f)

# Chuyển đổi tất cả biểu thức trong premises-FOL
for item in data:
    if "premises-FOL" in item:
        item["premises-FOL"] = [convert_fol_syntax(expr) for expr in item["premises-FOL"]]

# Ghi lại vào file train.json
with open(r'datasets/train.json', 'w', encoding='utf-8') as f:
    json.dump(data, f, ensure_ascii=False, indent=4)



def add_ids_to_json_items(file_path, output_path=None):
    with open(file_path, 'r', encoding='utf-8') as f:
        data = json.load(f)

    # Kiểm tra định dạng phù hợp (danh sách các dict)
    if not isinstance(data, list):
        raise ValueError("JSON must be a list of objects (dictionaries).")

    # Thêm id cho từng item
    for idx, item in enumerate(data):
        item['id_sample'] = idx

    # Ghi đè hoặc ghi vào file mới
    if output_path is None:
        output_path = file_path  # Ghi đè
    with open(output_path, 'w', encoding='utf-8') as f:
        json.dump(data, f, indent=4, ensure_ascii=False)

    print(f"✔ Đã thêm 'id' cho mỗi item và lưu vào: {output_path}")

add_ids_to_json_items(r'datasets/train.json', output_path=r'datasets/train.json')

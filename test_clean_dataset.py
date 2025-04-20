def convert_fol_syntax(expr):
    expr = expr.replace("->", "→")
    expr = expr.replace("'", "")
    expr = expr.replace("implies", "→")
    expr = expr.replace("not ", "¬")
    expr = expr.replace("~", "¬")
    expr = expr.replace("&", "∧")
    expr = expr.replace("|", "∨")
    expr = expr.replace("<=", "≤")
    expr = expr.replace(">=", "≥")
    expr = expr.replace("Hà", "Ha")
    expr = expr.replace("GPA4.0", "GPA4")
    expr = expr.replace("FORALL", "ForAll")
    expr = expr.replace("EXISTS", "Exists")
    expr = expr.replace(" in ", " ∈ ")

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

    return result + f'({expr})'



print(convert_fol_syntax(r"ForAll(x, (completed_core_curriculum(x) ∧ passed_science_assessment(x)) → qualified_for_advanced_courses(x))"))

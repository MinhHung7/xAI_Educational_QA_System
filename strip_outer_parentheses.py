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


print(strip_outer_parentheses("(((A ∧ B) ∨ C))"))
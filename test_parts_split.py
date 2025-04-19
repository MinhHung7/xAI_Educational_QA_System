def split_top_level(expr, delimiter='→'):
    depth = 0
    parts = []
    last = 0
    i = 0
    while i < len(expr):
        c = expr[i]
        if c == '(':
            depth += 1
        elif c == ')':
            depth -= 1
        elif expr[i:i+len(delimiter)] == delimiter and depth == 0:
            parts.append(expr[last:i].strip())
            last = i + len(delimiter)
            i += len(delimiter) - 1
        i += 1
    parts.append(expr[last:].strip())

    return parts

# Thử nghiệm
fol_str = "angle(A) + angle(B) + angle(C) = 180"


arrow_parts = split_top_level(fol_str, delimiter='+')
for part in arrow_parts:
    print(part)

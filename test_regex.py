import regex

fol_str = "Q(Const)"

match = regex.search(r"¬*\w+\((?:[^()]+|(?R))*\)", fol_str)
if match and not fol_str.startswith('∀'):
    pred = match.group()
    print(pred)
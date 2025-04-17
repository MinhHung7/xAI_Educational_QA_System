import regex

fol_str = "∀x(P(x, A) → Q(x, B))"

# Regex có hỗ trợ đệ quy
pattern = r"¬*\w+\((?:[^()]+|(?R))*\)"

match = regex.search(pattern, fol_str)

if match:
    print("✅ Match:", match.group())
else:
    print("❌ No match")

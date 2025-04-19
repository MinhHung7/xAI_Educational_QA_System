import re

pattern = r'''
^
\s*
(?P<lhs>
    \w+\([^\(\)]+\)                     # hàm có 1 hoặc nhiều đối số
    (?:\s*[\+\-]\s*\w+\([^\(\)]+\))*    # nhiều hàm cộng/trừ nhau
)
\s*=\s*
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

# Test
test_cases = [
    "angle(A) + angle(B) + angle(C) = 180",
    "f1(A) + f2(B) + f3(C) + f4(D) = 89.5",
    "P(A) - Q(B) + R(C) = angle(D)",
    "f(A) + g(B) = X",
    "angle(A) + angle(B) = angle(C) + angle(D)",
    "distance_product(intersections, centers) = radii_product(C1, C2)"
]

for fol_str in test_cases:
    match = re.match(pattern, fol_str, re.VERBOSE)
    print(f"'{fol_str}' =>", "✅ MATCH" if match else "❌ NO MATCH")

import json

# Các ký tự cần kiểm tra
special_chars = ['=', '≥', '>', '<', '≠', '≤', '+', '.', '∈', '*']

# Đọc file JSON đầu vào
with open(r'datasets/train.json', 'r', encoding='utf-8') as f:
    data = json.load(f)

# Lọc các item thỏa điều kiện
filtered_data = []
for item in data:
    if 'premises-FOL' in item:
        for sentence in item['premises-FOL']:
            if any(char in sentence for char in special_chars):
                filtered_data.append(item)
                break  # Thỏa mãn 1 câu là đủ, không cần kiểm tra tiếp

# Ghi kết quả ra file JSON đầu ra
with open(r'datasets/math_dataset.json', 'w', encoding='utf-8') as f:
    json.dump(filtered_data, f, ensure_ascii=False, indent=2)

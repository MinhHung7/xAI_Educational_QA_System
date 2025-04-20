import json

# Các ký tự cần kiểm tra
special_chars = ['=', '≥', '>', '<', '≠', '≤', '+', '.', '∈', '*']

# Đọc file train.json
with open(r'datasets/train.json', 'r', encoding='utf-8') as f:
    train_data = json.load(f)

# Đọc file math_dataset.json nếu đã tồn tại, ngược lại khởi tạo danh sách rỗng
math_data = []

# Tạo danh sách mới cho các item còn lại trong train_data
new_train_data = []

# Kiểm tra và phân loại từng item
for item in train_data:
    moved = False
    if 'premises-FOL' in item:
        for sentence in item['premises-FOL']:
            if any(char in sentence for char in special_chars):
                math_data.append(item)
                moved = True
                break  # Thỏa mãn 1 câu là đủ
    if not moved:
        new_train_data.append(item)

# Ghi lại file train.json đã được cập nhật (loại bỏ các item thỏa điều kiện)
with open(r'datasets/train.json', 'w', encoding='utf-8') as f:
    json.dump(new_train_data, f, ensure_ascii=False, indent=2)

# Ghi thêm vào math_dataset.json
with open(r'datasets/math_dataset.json', 'w', encoding='utf-8') as f:
    json.dump(math_data, f, ensure_ascii=False, indent=2)

print(f"Đã di chuyển {len(train_data) - len(new_train_data)} item thỏa điều kiện vào math_dataset.json.")

from sentence_transformers import SentenceTransformer
import faiss
import numpy as np
import json
import os

# Load model
model = SentenceTransformer("sentence-transformers/all-mpnet-base-v2")

# Load JSON
def load_json_dataset(filepath):
    try:
        if not os.path.exists(filepath):
            print(f"❌ Error: File not found at {filepath}")
            return None
        with open(filepath, 'r', encoding='utf-8') as f:
            data = json.load(f)
        print(f"✅ Successfully loaded data from {filepath}")
        return data
    except Exception as e:
        print(f"❌ An error occurred while loading {filepath}: {e}")
        return None

# Main logic with top-k results
def search_question_and_return_info(query, dataset_path, k=3):
    dataset = load_json_dataset(dataset_path)
    if dataset is None:
        return

    all_questions = [question for item in dataset for question in item["questions"]]
    question_embeddings = model.encode(all_questions, convert_to_numpy=True)

    index = faiss.IndexFlatL2(question_embeddings.shape[1])
    index.add(question_embeddings)

    query_embedding = model.encode([query], convert_to_numpy=True)
    D, I = index.search(query_embedding, k=k)

    print(f"\n🔍 Top {k} most similar questions to:")
    print(f"🧾 Query: \"{query}\"\n")

    for rank, matched_index in enumerate(I[0]):
        matched_question = all_questions[matched_index]
        print(f"🔹 Rank {rank+1}: \"{matched_question}\"")

        # Tìm item chứa câu hỏi
        for item in dataset:
            if matched_question in item["questions"]:
                q_idx = item["questions"].index(matched_question)
                print(f"  ✅ Answer: {item['answers'][q_idx]}")
                print(f"  💡 Explanation: {item['explanation'][q_idx]}")
                print(f"  📎 Premises:")
        print("─" * 50)

# Example usage
query = "Which statement about security systems can we conclude from the given information?\nA. Every security system with motion detection includes door sensors.\nB. Every security system with an alarm system detects motion.\nC. Some security systems lack video surveillance.\nD. Every security system with door sensors integrates with smart home devices."
dataset_path = r"datasets/train.json"
search_question_and_return_info(query, dataset_path, k=3)

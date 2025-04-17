import json
import os # Optional: Useful for constructing file paths

def load_json_dataset(filepath):
    """
    Loads data from a JSON file.

    Args:
        filepath (str): The full path to the JSON file.

    Returns:
        (list | dict | None): The loaded data (usually a list or dictionary),
                              or None if an error occurs during loading.
    """
    try:
        # Ensure the file exists before trying to open it
        if not os.path.exists(filepath):
            print(f"Error: File not found at {filepath}")
            return None

        # Open the file in read mode ('r') with UTF-8 encoding (common for JSON)
        with open(filepath, 'r', encoding='utf-8') as f:
            # Load the JSON data from the file
            data = json.load(f)
        print(f"Successfully loaded data from {filepath}")
        return data

    except json.JSONDecodeError as e:
        # Handle errors if the file is not valid JSON
        print(f"Error decoding JSON from {filepath}: {e}")
        return None
    except Exception as e:
        # Handle other potential errors (e.g., permissions)
        print(f"An unexpected error occurred while reading {filepath}: {e}")
        return None

# --- How to Use ---

if __name__ == "__main__":
    # !!! IMPORTANT: Replace this with the actual path to YOUR JSON file !!!
    dataset_file_path = 'datasets/train.json'

    # Load the data
    hackathon_data = load_json_dataset(dataset_file_path)

    # Check if data was loaded successfully
    if hackathon_data:
        # Now you can work with the data
        print(f"Data loaded is of type: {type(hackathon_data)}")

        # If it's a list, print the number of records
        if isinstance(hackathon_data, list):
            print(f"Number of records found: {len(hackathon_data)}")
            # You can inspect the first record (if the list is not empty)
            if len(hackathon_data) > 0:
                print("\nFirst record sample:")
                # Pretty print the first record for better readability
                print(json.dumps(hackathon_data[0], indent=2))
        # If it's a dictionary, print its keys
        elif isinstance(hackathon_data, dict):
            print(f"Dataset keys: {list(hackathon_data.keys())}")
            # Optionally print a small sample if needed
            # print(json.dumps(dict(list(hackathon_data.items())[:2]), indent=2)) # Example: Print first 2 items

    else:
        print("Failed to load dataset. Please check the file path and format.")
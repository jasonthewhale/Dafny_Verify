import os
import json

def save_json(file_path, content):
    with open(file_path, 'w') as outfile:
        json.dump(content, outfile)


def read_json_file(file_path):
    # Open and read the JSON file
    with open( file_path, 'r') as file:
        # Parse the contents of the file into a Python list of dictionaries
        data = json.load(file)
    return data

normal_datasets = read_json_file('dataset/normal_data/final_dataset_normal.json')
error_datasets = read_json_file('dataset/error_data/final_dataset_error.json')
explained_datasets = read_json_file('dataset/explained_data/final_dataset_explained.json')

combined_datasets = normal_datasets + error_datasets + explained_datasets
save_json('dataset/combined_dataset.json', combined_datasets)
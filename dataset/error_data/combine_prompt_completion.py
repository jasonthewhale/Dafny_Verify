import os
import json


def read_file(file_path):
	with open(file_path, 'r') as f:
		return f.read()

def write_file(file_path, content):
	with open(file_path, 'w') as f:
		f.write(content)
	

def save_json(file_path, content):
    with open(file_path, 'w') as outfile:
        json.dump(content, outfile)


all_prompt = os.listdir('./prompt')
all_completion = os.listdir('./completion')
all_prompt_files = [f for f in all_prompt if f.endswith('.dfy')]

dataset = []
for file in all_prompt_files:
    prefix = file.split('_error')[0]
    completion_file_path = './completion/' + prefix + '.dfy'
    prompt_file_path = './prompt/' + file
    prompt = read_file(prompt_file_path).strip()
    completion = read_file(completion_file_path).strip()

    data = {
	    'prompt': prompt,
	    'completion': completion
	}
    dataset.append(data)
save_json("./final_dataset_error.json", dataset)
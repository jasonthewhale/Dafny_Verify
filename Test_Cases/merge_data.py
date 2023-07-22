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


def read_json_file(file_path):
    # Open and read the JSON file
    with open( file_path, 'r') as file:
        # Parse the contents of the file into a Python list of dictionaries
        data = json.load(file)
    return data


dataset = []

# For explained dataset
prompt_directory = 'dataset/explained_data/prompt/'
completion_directory = 'dataset/explained_data/completion/'
all_prompt_files = os.listdir(prompt_directory)
prompt_files = [f for f in all_prompt_files if f.endswith('.dfy')]
all_completion_files = os.listdir(completion_directory)
completion_files = [c for c in all_completion_files if c.endswith('.dfy')]

for file in prompt_files:
	prompt_file_path = prompt_directory + file
	prompt = read_file(prompt_file_path)
	completion_file_path = completion_directory + file
	completion = read_file(completion_file_path)

	# save into another folder for reference
	write_file('dataset/explained_data/explained_dataset/' + file.replace('.dfy', '.txt'), 
		f'PROMPT:\n{prompt}\n\n\nCOMPLETION:\n{completion}')

	# save each pair of prompt and completion into a dictionary
	data = {
	'prompt': prompt,
	'completion': completion,
	}
	dataset.append(data)
	print(f'{file} is saved')
save_json('dataset/explained_data/' + 'final_dataset_explained.json', dataset)


# For normal dataset
# prompt_directory = 'dataset/normal_data/prompt/'
# completion_directory = 'dataset/normal_data/completion/'
# all_prompt_files = os.listdir(prompt_directory)
# prompt_files = [f for f in all_prompt_files if f.endswith('.dfy')]
# all_completion_files = os.listdir(completion_directory)
# completion_files = [c for c in all_completion_files if c.endswith('.dfy')]

# for file in prompt_files:
# 	prompt_file_path = prompt_directory + file
# 	prompt = read_file(prompt_file_path)
# 	completion_file_path = completion_directory + file
# 	completion = read_file(completion_file_path)

# 	# save into another folder for reference
# 	write_file('dataset/normal_data/normal_dataset/' + file.replace('.dfy', '.txt'), 
# 		f'PROMPT:\n{prompt}\n\n\nCOMPLETION:\n{completion}')

# 	# save each pair of prompt and completion into a dictionary
# 	data = {
# 	'prompt': prompt,
# 	'completion': completion,
# 	}
# 	dataset.append(data)
# 	print(f'{file} is saved')
# save_json('dataset/normal_data/' + 'final_dataset_normal.json', dataset)

# For error dataset
# 
# prompt_directory = 'dataset/error_data/prompt/'
# completion_directory = 'dataset/error_data/completion/'
# all_prompt_files = os.listdir(prompt_directory)
# prompt_files = [f for f in all_prompt_files if f.endswith('.dfy')]
# all_completion_files = os.listdir(completion_directory)
# completion_files = [c for c in all_completion_files if c.endswith('.dfy')]
# 
# for file in prompt_files:
# 	prefix = file.split('_')[0]
# 	prompt_file_path = prompt_directory + file
# 	prompt = read_file(prompt_file_path)
# 	completion_file_path = completion_directory + prefix + '.dfy'
# 	completion = read_file(completion_file_path)

# 	# save into another folder for reference
# 	write_file('dataset/error_data/error_dataset/' + file.replace('.dfy', '.txt'), 
# 		f'PROMPT:\n{prompt}\n\n\nCOMPLETION:\n{completion}')

# 	# save each pair of prompt and completion into a dictionary
# 	data = {
# 	'prompt': prompt,
# 	'completion': completion,
# 	}
# 	dataset.append(data)
# 	print(f'{file} is saved')

# save_json('dataset/error_data/' + 'final_dataset_error.json', dataset)





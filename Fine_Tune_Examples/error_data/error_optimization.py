import os
import subprocess

def read_file(file_path):
	with open(file_path, 'r') as f:
		return f.read()

def get_content_before_error(file_path):
    lines = []
    with open(file_path, 'r') as file:
        for line in file:
            if line.startswith('Error:'):
                break
            lines.append(line)
    return ''.join(lines)

def write_file(file_path, content):
	with open(file_path, 'w') as f:
		f.write(content)

def verify(file_path, command='dafny -showSnippets:1 '):
    cli = command + file_path
    process = subprocess.Popen(cli, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    # Wait for the process to finish and get the output
    stdout, stderr = process.communicate()

    # Decode the output from bytes to string
    stdout = stdout.decode()
    stderr = stderr.decode()
    return stdout

def optimize_error_message(ori_error_message):
	lines = ori_error_message.split('\n')
	explanations = []
	codes = []
	indexes = []
	result_line = ''
	for line in lines:
		if '): ' in line:
			line = line.split('): ')[1]
			explanations.append(line)
		elif line and line[0].isdigit():
			codes.append(line)
		elif '^' in line:
			start = line.index('^')
			end = line.rindex('^') + 1
			indexes.append([start, end])
		elif 'Dafny program verifier' in line:
			result_line = line
	optimised_message = ''
	for i in range(len(codes)):
		related_code = codes[i][indexes[i][0]:indexes[i][1]]
		line_code = codes[i].split("| ", 1)[1].strip()
		code_message = f"'{related_code}' in '{line_code}'"
		optimised_message += f"{code_message}" + ": " + explanations[i] + '\n'

	optimised_message = 'Error:\n' + optimised_message + result_line
	return optimised_message

'''
directory = 'dataset/error_data/prompt/'
all_files = os.listdir(directory)
dfy_files = [f for f in all_files if f.endswith('.dfy')]

for file in dfy_files:
	# prefix = file.split('_error')[0]
	file_path = directory + file
	content = read_file(file_path)
	if 'Error' not in content:
		# code = get_content_before_error(file_path).strip()
		# write_file(file_path, code)
		ori_error_message = verify(file_path)
		# try:
		optimised_message = optimize_error_message(ori_error_message).strip()
		write_file(file_path, content + '\n\n' + optimised_message)
		# write_file(file_path, code + '\n\n' + optimised_message)
		print(f'{file} is improved')
		# except Exception as e:
		# 	print(f'Met error when improving: {file}', e)

'''



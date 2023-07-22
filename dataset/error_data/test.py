import os
import itertools

def read_file(file_path):
    with open(file_path, 'r') as f:
        file_content = f.read()
    return file_content

def save_file(file_path, content):
    with open(file_path, 'w') as f:
        f.write(content)
    
def main():
    file_names = os.listdir("./")
    for file_name in file_names:
        if file_name.endswith(".dfy"):
            code_with_invariant = read_file(file_name)
            lines = code_with_invariant.split("\n")
            invariant_lines = [i for i, line in enumerate(lines) if 'invariant' in line]
            combinations = []
            for r in range(1, len(invariant_lines) + 1):
                combinations.extend(itertools.combinations(invariant_lines, r))
            for i, combination in enumerate(combinations):
                # Get all lines except the ones in the current combination
                new_lines = [line for j, line in enumerate(lines) if j not in combination]
                new_code = '\n'.join(new_lines)
                new_file_name = file_name.replace(".dfy", f"_{i+1}.txt")
                save_file('./prompt/' + new_file_name, new_code)
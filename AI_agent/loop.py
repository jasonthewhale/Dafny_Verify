import os
import json
import time
import openai
import subprocess

os.environ['OPENAI_API_KEY'] = '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'
openai.api_key = os.getenv("OPENAI_API_KEY")


def turbo_completion(messages):
    completion = ""
    max_retry = 5
    retry = 0
    messages=messages
    try:
        completion = openai.ChatCompletion.create(
            model="gpt-3.5-turbo",
            messages=messages,
            temperature=0,
            max_tokens=512,
        )
        reply = completion.choices[0].message['content']
        if '```dafny\n' in reply:
            code_start = reply.find('```dafny')
            code_end = reply.rfind('```')
            reply = reply[code_start+8:code_end]
        return reply
    except Exception as overload:
        retry += 1
        if retry >= max_retry:
            return "turbo error: %s" %overload
    

def read_file(file_path):
    with open(file_path, 'r') as f:
        return f.read()
    

def save_file(file_path, content):
    with open(file_path, 'w') as f:
        f.write(content)


def save_json(file_path, content):
    with open(file_path, 'w') as outfile:
        json.dump(content, outfile)


def verify(file_path, command):
    cli = command + file_path
    process = subprocess.Popen(cli, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    # Wait for the process to finish and get the output
    stdout, stderr = process.communicate()

    # Decode the output from bytes to string
    stdout = stdout.decode()
    stderr = stderr.decode()
    return stdout

def main(file_name):
    test_file_path = '../Test_Cases/' + file_name + '.dfy'
    method = read_file(test_file_path)
    system_message = f"""
Complete missing loop invariant for this method. Since your response will be tested with verifier\
, pls be careful and accurate. 

Valid dafny code only. Do not apologize or explain when making mistakes. Remeber put full complete \
method into a single code block and return this the code block as your response.
    """
    messages=[
          {"role": "system", "content": system_message},
          {"role": "user", "content": method}
        ]

    completion = turbo_completion(messages)
    loop_seq = 1
    generated_file_path = f'../Generated_Code/{file_name}_{loop_seq}.dfy'
    save_file(generated_file_path, completion)
    test_result = verify(generated_file_path, 'dafny verify ')
    valid_string = 'verified, 0 errors'

    while valid_string not in test_result:
        dir_path = '/Users/youjunchen/Desktop/Dafny/Generated_Code/'
        error_message = test_result.replace(dir_path, "")
        print(f'\033[91mFailed in seq: {loop_seq}\033[0m\n{error_message}\n\n')
        generated_file_path = f'../Generated_Code/{file_name}_{loop_seq}.dfy'
        save_file(generated_file_path, completion)
        messages.append({"role": "assistant", "content": completion})
        messages.append({"role": "user", "content": 'But verifier gave error: ' + error_message})
        save_json(f'./chat_log/{file_name}_{loop_seq}.json', messages)
        loop_seq += 1
        time.sleep(10)
        completion = turbo_completion(messages)
        test_result = verify(generated_file_path, 'dafny /trace ')
    print(f'\033[92mSucceed in seq: {loop_seq}\033[0m\n{test_result}')

    

   
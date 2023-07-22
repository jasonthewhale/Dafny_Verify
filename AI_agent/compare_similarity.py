import os
import json
import openai
import numpy as np
from numpy.linalg import norm

openai.api_key = 'API_KEY'

def gpt3_embedding(content, engine='text-similarity-ada-001'):
    content = content.encode(encoding='ASCII', errors="ignore").decode()
    response = openai.Embedding.create(input=content,engine=engine)
    vector = response['data'][0]['embedding'] 
    return vector

def read_file(file_path):
    with open(file_path, 'r') as f:
        return f.read()
    
def read_json(file_path):
    with open(file_path, 'r') as f:
        return json.load(f)

def save_json(filepath, payload):
    with open(filepath, 'w', encoding='utf-8') as outfile:
        json.dump(payload, outfile, ensure_ascii=False, sort_keys=True, indent=2)

def similarity(vector1, vector2):
    return np.dot(vector1,vector2)/(norm(vector1)*norm(vector2))

# Create vectors for verification examples
# correct_examples = os.listdir('verify_examples')
# correct_dfy = [d for d in correct_examples if d.endswith('.dfy')]
# for dfy in correct_dfy:
#     vector = gpt3_embedding(read_file('verify_examples/'+dfy))
#     save_json('vectors/correct/'+dfy[:-4]+'.json', vector)

def create_vector_for_pre(name):
    dfy_code = read_file('temp.dfy')
    vector = gpt3_embedding(dfy_code)
    save_json('vectors/pre_fine_tune/'+ name +'.json', vector)

def create_vector_for_post(name):
    dfy_code = read_file('temp.dfy')
    vector = gpt3_embedding(dfy_code)
    save_json('vectors/post_fine_tune/'+ name +'.json', vector)

def create_vector_for_turbo(name):
    dfy_code = read_file('temp.dfy')
    vector = gpt3_embedding(dfy_code)
    save_json('vectors/turbo/'+ name +'.json', vector)


def compare_pre_and_correct():
    pre_files = os.listdir('vectors/pre_fine_tune')
    valid_pre_files = [d for d in pre_files if d.endswith('.json')]
    correct_files = os.listdir('vectors/correct')
    valid_correct_files = [d for d in correct_files if d.endswith('.json')]
    for pre in valid_pre_files:
        for correct in valid_correct_files:
            if pre == correct:
                pre_vector = read_json('vectors/pre_fine_tune/'+pre)
                correct_vector = read_json('vectors/correct/'+correct)
                score = similarity(pre_vector, correct_vector)
                print(f"{pre}'s pre and correct similarity is: {score}")


def compare_post_and_correct():
    post_files = os.listdir('vectors/post_fine_tune')
    valid_post_files = [d for d in post_files if d.endswith('.json')]
    correct_files = os.listdir('vectors/correct')
    valid_correct_files = [d for d in correct_files if d.endswith('.json')]
    for post in valid_post_files:
        for correct in valid_correct_files:
            if post == correct:
                post_vector = read_json('vectors/post_fine_tune/'+post)
                correct_vector = read_json('vectors/correct/'+correct)
                score = similarity(post_vector, correct_vector)
                print(f"{post}'s post and correct similarity is: {score}")


def compare_turbo_and_correct():
    turbo_files = os.listdir('vectors/turbo')
    valid_turbo_files = [d for d in turbo_files if d.endswith('.json')]
    correct_files = os.listdir('vectors/correct')
    valid_correct_files = [d for d in correct_files if d.endswith('.json')]
    for turbo in valid_turbo_files:
        for correct in valid_correct_files:
            if turbo == correct:
                turbo_vector = read_json('vectors/turbo/'+turbo)
                correct_vector = read_json('vectors/correct/'+correct)
                score = similarity(turbo_vector, correct_vector)
                print(f"{turbo}'s turbo and correct similarity is: {score}")
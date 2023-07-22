import os

# Specify the directory where your files are located
directory = "./completion"

for filename in os.listdir(directory):
    if filename.endswith(".txt"):
        # Split the file extension and get the root name
        root = os.path.splitext(filename)[0]
        # Rename the file
        os.rename(os.path.join(directory, filename), os.path.join(directory, root + ".dfy"))
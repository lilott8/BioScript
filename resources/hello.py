import json

file = open('storage.json')
info = json.loads(file.read())
print(info)

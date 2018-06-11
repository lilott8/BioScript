import json


#creates a sparse_matrix dictionary w/ (key = id), value = dictionary of ( key = id, value = outcome)
def create_sparse_matrix(file_name):
    file_read = open(file_name)
    json_dict = json.loads(file_read.read())['chemicalgroups']['group']
    sparse_matrix = {}

    for json_item in json_dict:  #json_dict is NOT a dict.... the .items() function doesn't work!!!
        if 'reactivegroups' in json_item and json_item['reactivegroups'] != None and len(json_item['reactivegroups']) != 0:
            key   = int(json_item['id'])
            value = {}
            
            #horrible naming convention...find a better one....
            for j in json_item['reactivegroups']['reaction']:
                if ('id' in j) and ('outcome' in j): #and (j['outcome'] == 'N'):
                    value[int(j['id'])] = j['outcome']

            sparse_matrix[key] = value


    return sparse_matrix


def check_sparse_matrix(sparse_matrix, x, y):
    return x in sparse_matrix and y in sparse_matrix[x]



sparse_matrix = create_sparse_matrix(r"C:\Users\Daniel Tan\Documents\ChemType\resources\epa.json") #id's and list
print(check_sparse_matrix(sparse_matrix, 3, 1))
print(sparse_matrix[100][20])



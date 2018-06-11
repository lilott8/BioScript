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


#convert Java 448-480 lines to python....
#one-to-one conversion might not be possible...depending on how it might be implemented...
#types == set
def look_up_type(types, reaction_matrix):
    results = set()
    for t1 in types:
        for t2 in types:
            results.update(look_up_a_b(t1, t2, reaction_matrix))

    return results


def look_up_a_b(a, b, reaction_matrix):
    if a > b:
        a, b = b, a

    if a in reaction_matrix and b in reaction_matrix[a]:
        return map(lambda x: get_type_from_id(x), reaction_matrix[a][b])
    else:
        return {get_type_from_id(a), get_type_from_id(b)}


def get_type_from_id(x):
    return 100



print(look_up_type({1, 2, 3}, {1: {2: {1,2,3,4,5}}}))


#sparse_matrix = create_sparse_matrix(r"C:\Users\Daniel Tan\Documents\ChemType\resources\epa.json") #id's and list
#print(check_sparse_matrix(sparse_matrix, 3, 1))
#print(sparse_matrix[100][20])



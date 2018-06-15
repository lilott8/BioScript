import json

class EpaManager(object):
    #creates a sparse_matrix dictionary w/ (key = id), value = dictionary of ( key = id, value = outcome)
    def create_sparse_matrix(file_name):
        json_dict = []
        sparse_matrix = {}

        with open(file_name) as file_read:
            json_dict = json.loads(file_read.read())['chemicalgroups']['group']

        for json_item in json_dict:  #json_dict is NOT a dict.... the .items() function doesn't work!!!
            if 'reactivegroups' in json_item and json_item['reactivegroups'] != None and len(json_item['reactivegroups']) != 0:
                key   = int(json_item['id'])
                value = dict(map(lambda x: (int(x['id']), x['outcome']), \
                    filter(lambda y: 'id' in y and 'outcome' in y, json_item['reactivegroups']['reaction']) ))
                sparse_matrix[key] = value

        return sparse_matrix


    def check_sparse_matrix(sparse_matrix, x, y):
        return x in sparse_matrix and y in sparse_matrix[x]


    def for_each_sparse_matrix_item(sparse_matrix, f):
        for x, yy in sparse_matrix.items():
            for y, c in yy.items():
                f(x, y, c)




import json

#hard-coded "hacky" kind of code...kind of works for now...maybe there's better
#way to do it????
#this function returns a list of dictionaries of all the attributes of a
#json object
def extract_chem_objects(json_string):
    json_dict = json.loads(json_string)
    for k, v in json_dict.items():
        for kk, vv, in v.items():
            return vv

#creates a sparse_matrix dictionary w/ key = id, value = reaction_list (id: xxx, outcome: yyy)
def create_sparse_matrix(chem_objects):
    sparse_matrix = {}
    for chem in chem_objects:
        if 'reactivegroups' in chem:
            #Hacky but doable...
            chem_group = chem['reactivegroups']
            if chem_group != None and 'reaction' in chem_group:
                sparse_matrix[chem['id']] = chem_group['reaction']
                
                for x in chem_group['reaction']:
                    for yyyy in x:
                        print(len(yyyy))


    return sparse_matrix


file_read = open(r"C:\Users\Daniel Tan\Documents\ChemType\resources\epa.json")
sparse_matrix = create_sparse_matrix(extract_chem_objects(file_read.read())) #id's and list
#for key_id, reaction_list in sparse_matrix.items():
#    print('Group Key ID: ', key_id)
#    print(reaction_list)

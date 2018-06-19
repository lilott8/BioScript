import json
import sys
import logging

if __name__ == '__main__': 
    string = sys.path[0][:-10] #add main directory to the system path, so we can have the 'enums'
    sys.path.append(string)

from enums.Consequence import Consequence


#this tests whether we can initialize and use the EpaManager
class EpaManager(object):

    __sparse_matrix = {}

    #constructor
    def __init__(self, file_name):
        self.__sparse_matrix = self.create_sparse_matrix(file_name)


    #creates a sparse_matrix dictionary w/ (key = id), value = dictionary of ( key = id, value = outcome)
    def create_sparse_matrix(self, file_name):
        json_parsed_struct = []
        sparse_matrix      = {}

        with open(file_name) as file_read:
            json_parsed_struct = json.loads(file_read.read())['chemicalgroups']['group']

        for json_item in json_parsed_struct:
            if 'reactivegroups' in json_item and json_item['reactivegroups'] != None and len(json_item['reactivegroups']) != 0:
                key   = int(json_item['id'])
                value = dict(map(lambda x: (int(x['id']), {'outcome':x['outcome']}), \
                    filter(lambda y: 'id' in y and 'outcome' in y, json_item['reactivegroups']['reaction'])))
                sparse_matrix[key] = value
        return sparse_matrix


    def check_sparse_matrix(self, x, y):
        return x in self.__sparse_matrix and y in self.__sparse_matrix[x]


    def for_each_sparse_matrix_item(self, f):
        for x, yy in self.__sparse_matrix.items():  
            for y, c in yy.items():
                f(x, y, c)

    #based off of the java consequence enum values
    def get_sparse_matrix_reaction(self, x, y):
        val = self.__sparse_matrix[x][y]['outcome']
        if val == 'N':
            return Consequence.INCOMPATIBLE
        elif val == 'C':
            return Consequence.CAUTION
        elif val == 'SR':
            return Consequence.SELF_REACTIVE
        else:
            return Consequence.UNKNOWN


    def get_sparse_matrix_at_index(self, x, y):
        return self.__sparse_matrix[x][y]


    def look_up_types(self, types):
        results = set()
        for t1 in types:
            for t2 in types:
                results.update(self.look_up_a_b(t1, t2))
                logging.info(results)
        return results


    def look_up_a_b(self, a, b):
        if a > b:
            a, b = b, a

        if a in self.__sparse_matrix and b in self.__sparse_matrix[a]:
            return set(map(Consequence.get_type_from_id, self.__sparse_matrix[a][b]['outcome']))
        else:
            return {Consequence.get_type_from_id(a), Consequence.get_type_from_id(b)}


def __test_():
    #make sure we can successfully initialize the EpaManager
    e = EpaManager(sys.path[0][:-10] + r'/resources/epa.json')
    results = e.look_up_types({1, 2, 3})
    #e.for_each_sparse_matrix_item(lambda x, y, c: logging.info('{0:5}, {1:5}: {2}'.format(x, y, c)))
    logging.info(results)


if __name__ == '__main__': 
    logging.basicConfig(level = logging.DEBUG)
    __test_()




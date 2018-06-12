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
    return x


'''
I don't know if we need it....
class ChemTypes:
    ACIDS_STRONG_NON_OXIDIZING      = 1
    ACIDS_STRONG_OXIDIZING          = 2
    ACIDS_CARBOXYLIC                = 3
    ALCOHOLDS_AND_POLYOLS           = 4
    ALDEHYDES                       = 5
    AMIDES_AND_IMIDES               = 6
    AMINES_PHOSPHINES_AND_PYRIDINES = 7
    AZO_DIAZO_AZIDO_HYDRAZINE_AND_AZIDE_COMPOUNDS = 8
    CARBAMATES                      = 9
    BASES_STRONG = 10
    CYANIDES_INORGANIC = 11
    THIOCARBAMATE_ESTERS_AND_SALTS_DIHIOCARBAMATE_ESTERS_AND_SALTS = 12
    ESTERS_SULFATE_ESTERS_PHOSPHATE_ESTERS_THIOPHOSPHATE_ESTERS_AND_BORATE_ESTERS = 13
    ETHERS = 14
    FLUORIDES_INORGANIC = 15
    HYDROCARBONS_AROMATIC = 16
    HALOGENATED_ORGANIC_COMPOUNDS = 17
    ISOCYANTES_AND_ISOTHIOCYANATES = 18
    KETONES = 19
    SULFIDES_ORGANIC = 20
    METALS_ALKALI_VERY_ACTIVE = 21
    METALS_ELEMENTAL_AND_POWDER_ACTIVE = 22
'''

#python enum is called by: x = Consequence(Consequence.H)
class Consequence:
    H   = 0
    F   = 1
    G   = 2
    GT  = 3
    GF  = 4
    E   = 5
    P   = 6
    S   = 7
    U   = 8
    WRS = 9
    N   = 10
    C   = 11
    SR  = 12

    def __init__(self, Type):
        self.value = Type

    #toString() from Java, if you will...
    def __str__(self):
        if self.value == Consequence.H:
            return "Head Generation"
        elif self.value == Consequence.F:
            return "Fire"
        elif self.value == Consequence.G:
            return "Innocuous and non-Flammable Gas generation"
        elif self.value == Consequence.GT:
            return "Toxic Gas Formation"
        elif self.value == Consequence.GF:
            return "Flammable Gas Formation"
        elif self.value == Consequence.E:
            return "Explosion"
        elif self.value == Consequence.P:
            return "Violent Polymerization"
        elif self.value == Consequence.S:
            return "Solubilization of Toxic Substance"
        elif self.value == Consequence.U:
            return "Unknown"
        elif self.value == Consequence.WRS:
            return "Water Reactive Substance"
        elif self.value == Consequence.N:
            return "Incompatible"
        elif self.value == Consequence.C:
            return "Caution"
        elif self.value == Consequence.SR:
            return "Self Reactive"
        else:
            return "????"








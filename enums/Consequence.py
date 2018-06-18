from enum import Enum

#python enum is called by: x = Consequence.HEAD_GENERATION
class Consequence(Enum):
    HEAD_GENERATION   = 0
    FIRE   = 1
    INNOCUOUS_AND_NON_FLAMMABLE_GAS_GENERATION = 2
    TOXIC_GAS_FORMATION  = 3
    FLAMMABLE_GAS_FORMATION = 4
    EXPLOSION   = 5
    VIOLENT_POLYMERIZATION = 6
    SOLUBILIZATION_OF_TOXIC_SUBSTANCE = 7
    UNKNOWN = 8
    WATER_REACTIVE_SUBSTANCE = 9
    INCOMPATIBLE = 10
    CAUTION = 11
    SELF_REACTIVE  = 12

    #dummy function for now...
    def get_type_from_id(x):
        return x

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
            return map(Problem.get_type_from_id, reaction_matrix[a][b])
        else:
            return {Problem.get_type_from_id(a), Problem.get_type_from_id(b)}



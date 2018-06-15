from enum import Enum

#python enum is called by: x = Consequence(Consequence.H)
class Consequence(Enum):
    Head_Generation   = 0
    Fire   = 1
    Innocuous_and_Non_Flammable_Gas_Generation   = 2
    Toxic_Gas_Formation  = 3
    Flammable_Gas_Formation  = 4
    Explosion   = 5
    Violent_Polymerization   = 6
    Solubilization_of_Toxic_Substance   = 7
    Unknown   = 8
    Water_Reactive_Substance = 9
    Incompatible   = 10
    Caution   = 11
    Self_Reactive  = 12

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



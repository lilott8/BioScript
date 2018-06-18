from enum import Enum

#python enum is called by: x = Consequence.HEAT_GENERATION
class Consequence(Enum):
    HEAT_GENERATION   = 0
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


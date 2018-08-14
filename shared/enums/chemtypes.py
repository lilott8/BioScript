from enum import IntEnum


class ChemTypes(IntEnum):
    UNKNOWN = -1
    MODULE = 0
    MAT = 1
    NAT = 2
    REAL = 3
    BOOL = 4


class Consequence(IntEnum):
    HEAT_GENERATION = 0
    FIRE = 1
    INNOCUOUS_AND_NON_FLAMMABLE_GAS_GENERATION = 2
    TOXIC_GAS_FORMATION = 3
    FLAMMABLE_GAS_FORMATION = 4
    EXPLOSION = 5
    VIOLENT_POLYMERIZATION = 6
    SOLUBILIZATION_OF_TOXIC_SUBSTANCE = 7
    UNKNOWN = 8
    WATER_REACTIVE_SUBSTANCE = 9
    INCOMPATIBLE = 10
    CAUTION = 11
    SELF_REACTIVE = 12

    def get_type_from_id(self, x):
        return x

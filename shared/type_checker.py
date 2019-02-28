from chemicals.epa_manager import EpaManager
from shared.enums.chemtypes import *
from shared.enums.config_flags import TypeCheckLevel


class TypeChecker(object):

    def __init__(self, level: TypeCheckLevel, epa: EpaManager):
        self.checker = level
        self.epa = epa

    def typecheck(self, one, two) -> set:
        if self.checker == TypeCheckLevel.DISABLED:
            return set()
        elif self.checker == TypeCheckLevel.NAIVE:
            return self.naive(one, two)
        elif self.checker == TypeCheckLevel.UNION:
            return self.union(one, two)
        else:
            return set()

    def union(self, one, two):
        return self.epa.get_interaction_result(one, two)

    def naive(self, one, two):
        result = set()
        if one in ChemTypeResolver.materials and two in ChemTypeResolver.materials:
            result.add(ChemTypes.MAT)
        elif one in ChemTypeResolver.numbers and two in ChemTypeResolver.numbers:
            result.union(ChemTypeResolver.numbers)
        elif (one in ChemTypeResolver.numbers and two in ChemTypeResolver.materials) or \
                (one in ChemTypeResolver.materials and two in ChemTypeResolver.numbers):
            result.add(ChemTypes.REAL)
            result.add(ChemTypes.MAT)
        else:
            result.add(ChemTypes.UNKNOWN)
        return result

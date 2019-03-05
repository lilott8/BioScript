from enum import IntEnum

from chemicals.chemtypes import ChemTypes, ChemTypeResolver
from chemicals.epa_manager import EpaManager


class TypeCheckLevel(IntEnum):
    NAIVE = 1
    UNION = 2


class CombineMethod(IntEnum):
    NAIVE = 1
    SIMULATE = 2

    def get_combiner(self, epa_defs: str, abs_int: str):
        if self.value == CombineMethod.SIMULATE:
            return SimulateCombiner()
        else:
            return NaiveCombiner(epa_defs, abs_int)


class Combiner(object):
    """
    This class deals with combining chemicals.
    However, there is a difficult dependency to untie here.
    Functions typecheck, union, and naive could be split into
    their own class (TypeChecker) but for simplicity, right now,
    it is just combined here.
    """

    def __init__(self, epa_manager: str = "/resources/epa_defs.json",
                 checker: TypeCheckLevel = TypeCheckLevel.NAIVE,
                 abs_int: str = '/resources/abstract-interaction.txt'):
        self.epa_manager = EpaManager(epa_manager, abs_int)
        self.checker = checker

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
        return self.epa_manager.get_interaction_result(one, two)

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

    def combine(self, *args: list) -> set:
        """
        Takes a list of sets and returns a union of them.
        :param args: List of sets containing ChemTypes types.
        :return: Set of union-ed ChemTypes types.
        """
        raise NotImplementedError

    def combine_sets(self, set1: set, set2: set) -> set:
        raise NotImplementedError

    def combine_types(self, t1: ChemTypes, t2: ChemTypes) -> set:
        raise NotImplementedError


class NaiveCombiner(Combiner):

    def __init__(self, epa_manager: str = "NAIVE./resources/epa_defs.json",
                 abs_int: str = 'NAIVE./resources/abstract-interaction.txt'):
        super().__init__(epa_manager=epa_manager, abs_int=abs_int)

    def combine(self, *args: set) -> set:
        types = set()
        for arg in args:
            types.union(arg)
        return types

    def combine_sets(self, set1: set, set2: set) -> set:
        result = set()
        for t1 in set1:
            for t2 in set2:
                result.union(self.checker.typecheck(t1, t2))
                # if self.config.typecheck == TypeChecker.UNION:
                #     result.union(self.epa_manager.get_interaction_result(t1, t2))
                # else:
                #     result.union(self.combine_types(t1, t2))
        return result

    def combine_types(self, t1: ChemTypes, t2: ChemTypes) -> set:
        return self.checker.typecheck(t1, t2)


class SimulateCombiner(Combiner):

    def __init__(self):
        super().__init__()

    def combine(self, *args: set) -> set:
        return set()

    def combine_sets(self, t1: set, t2: set) -> set:
        return set()

    def combine_types(self, t1: ChemTypes, t2: ChemTypes) -> set:
        pass

from chemicals.epa_manager import EpaManager
from shared.enums.chemtypes import ChemTypes
from shared.type_checker import TypeChecker
from shared.variable import Chemical


class Combiner(object):

    def __init__(self, config: 'Config'):
        self.config = config
        self.epa_manager = EpaManager(config.epa_defs, config.abstract_interaction)
        self.checker = TypeChecker(self.config.typecheck, self.epa_manager)

    def combine(self, *args: list) -> set:
        """
        Takes a list of sets and returns a union of them.
        :param args: List of sets containing ChemTypes types.
        :return: Set of union-ed ChemTypes types.
        """
        raise NotImplementedError

    def combine_variables(self, var1: Chemical, var2: Chemical) -> set:
        raise NotImplementedError

    def combine_sets(self, set1: set, set2: set) -> set:
        raise NotImplementedError

    def combine_types(self, t1: ChemTypes, t2: ChemTypes) -> set:
        raise NotImplementedError

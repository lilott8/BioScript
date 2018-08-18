import colorlog

from chemicals.epa_manager import EpaManager
from config.config import Config
from shared.enums.chemtypes import ChemTypes
from shared.variable import Variable


class Combiner(object):

    def __init__(self):
        self.log = colorlog.getLogger(__name__)
        self.config = Config.getInstance()
        self.epa_manager = EpaManager(self.config.epa_defs, self.config.abstract_interaction)

    def combine(self, *args: list) -> set:
        """
        Takes a list of sets and returns a union of them.
        :param args: List of sets containing ChemTypes types.
        :return: Set of union-ed ChemTypes types.
        """
        raise NotImplementedError

    def combine_variables(self, var1: Variable, var2: Variable) -> set:
        raise NotImplementedError

    def combine_sets(self, set1: set, set2: set) -> set:
        raise NotImplementedError

    def combine_types(self, t1: ChemTypes, t2: ChemTypes) -> set:
        raise NotImplementedError

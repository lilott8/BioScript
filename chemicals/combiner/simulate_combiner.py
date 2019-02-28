from chemicals.combiner.combiner import Combiner
from shared.enums.chemtypes import ChemTypes
from shared.variable import Chemical


class SimulateCombiner(Combiner):

    def __init__(self, config):
        super().__init__(config)

    def combine(self, *args: set) -> set:
        return set()

    def combine_variables(self, var1: Chemical, var2: Chemical) -> set:
        return set()

    def combine_sets(self, t1: set, t2: set) -> set:
        return set()

    def combine_types(self, t1: ChemTypes, t2: ChemTypes) -> set:
        pass

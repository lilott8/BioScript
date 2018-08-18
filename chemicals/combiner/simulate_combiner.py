from chemicals.combiner.combiner import Combiner
from chemicals.epa_manager import EpaManager
from shared import Variable


class SimulateCombiner(Combiner):

    def __init__(self, epa_manager: EpaManager):
        super().__init__(epa_manager)

    def combine(self, *args: set) -> set:
        self.log.warning("Not doing anything with this.")
        return set()

    def combine_variables(self, var1: Variable, var2: Variable) -> set:
        self.log.warning("Not doing anything with this.")
        return set()

    def combine_sets(self, t1: set, t2: set) -> set:
        self.log.warning("Not doing anything with this.")
        return set()

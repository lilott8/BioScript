from chemicals.combiner.combiner import Combiner
from shared import Variable
from shared.enums.chemtypes import ChemTypes


class NaiveCombiner(Combiner):

    def __init__(self, config: 'Config'):
        super().__init__(config)

    def combine(self, *args: set) -> set:
        types = set()
        for arg in args:
            types.union(arg)
        return types

    def combine_variables(self, var1: Variable, var2: Variable) -> set:
        return self.combine_sets(var1.types, var2.types)

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
        # if self.config.typecheck == TypeChecker.UNION:
        #     return self.epa_manager.get_interaction_result(t1, t2)
        # else:
        #
        # return result

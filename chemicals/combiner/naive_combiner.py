from chemicals.combiner.combiner import Combiner
from shared import Variable
from shared.enums.chemtypes import ChemTypeResolver
from shared.enums.chemtypes import ChemTypes
from shared.enums.config_flags import TypeChecker


class NaiveCombiner(Combiner):

    def __init__(self):
        super().__init__()

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
                if self.config.typecheck == TypeChecker.UNION:
                    result.union(self.epa_manager.get_interaction_result(t1, t2))
                else:
                    result.union(self.combine_types(t1, t2))
        return result

    def combine_types(self, t1: ChemTypes, t2: ChemTypes) -> set:
        if self.config.typecheck == TypeChecker.UNION:
            return self.epa_manager.get_interaction_result(t1, t2)
        else:
            result = set()
            if t1 in ChemTypeResolver.materials and t2 in ChemTypeResolver.materials:
                result.add(ChemTypes.MAT)
            elif t1 in ChemTypeResolver.numbers and t2 in ChemTypeResolver.numbers:
                result.union(ChemTypeResolver.numbers)
            else:
                result.add(ChemTypes.UNKNOWN)
        return result

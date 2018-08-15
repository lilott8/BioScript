from chemicals.combiner.combiner import Combiner


class NaiveCombiner(Combiner):

    def __init__(self):
        super().__init__()

    def combine(self, *args: set) -> set:
        types = set()
        for arg in args:
            types.union(arg)
        return types

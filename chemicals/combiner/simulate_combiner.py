from chemicals.combiner.combiner import Combiner


class SimulateCombiner(Combiner):

    def __init__(self):
        super().__init__()

    def combine(self, *args: set) -> set:
        self.log.warning("Not doing anything with this.")
        return {}

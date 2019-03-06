from compiler.data_structures import Program
from compiler.targets.base_target import BaseTarget


class PuddleTarget(BaseTarget):

    def __init__(self, configuration):
        super().__init__(configuration, "PuddleTarget")

    def transform(self, program: Program):
        return False

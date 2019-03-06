from compiler.data_structures.program import Program
from compiler.targets.base_target import BaseTarget


class MFSimTarget(BaseTarget):

    def __init__(self, configuration: 'Config'):
        super().__init__(configuration, "MFSimTarget")

    def transform(self, program: Program):
        return False

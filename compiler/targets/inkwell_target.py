from compiler.data_structures import Program
from compiler.targets.base_target import BaseTarget


class InkwellTarget(BaseTarget):

    def __init__(self, configuration: 'Config'):
        super().__init__(configuration, "InkwellTarget")

    def transform(self, program: Program):
        return False

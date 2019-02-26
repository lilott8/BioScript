from compiler.data_structures.bs_program import BSProgram
from compiler.targets.base_target import BaseTarget


class InkwellTarget(BaseTarget):

    def __init__(self, program: BSProgram):
        super().__init__(program, "InkwellTarget")

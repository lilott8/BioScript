from compiler.data_structures.bs_program import BSProgram
from compiler.targets.base_target import BaseTarget


class MFSimTarget(BaseTarget):

    def __init__(self, program: BSProgram):
        super().__init__(program, "MFSimTarget")

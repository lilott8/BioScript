from compiler.data_structures.bs_program import BSProgram
from compiler.passes.transforms.bs_transform import BSTransform


class SplitEdges(BSTransform):

    def __init__(self):
        super().__init__("Split Edges")

    def transform(self, program: BSProgram):
        pass

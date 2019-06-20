from compiler.data_structures.program import Program
from compiler.passes.transforms.bs_transform import BSTransform


class SplitEdges(BSTransform):

    def __init__(self):
        super().__init__("Split Edges")

    def transform(self, program: Program) -> Program:
        return program

from compiler.data_structures import Program
from compiler.passes.transforms.bs_transform import BSTransform


class Inline(BSTransform):

    def __init__(self):
        super().__init__("inliner")

    def transform(self, program: Program) -> Program:
        """
        This function will do three things:
        1) Run alpha conversion on non-recursive calls,
        2) Alter the call graph, and edge connections of the graph,
        3) Alter the jumps in the basic blocks.
        :param program: The program requiring modification.
        :return: The modified program.
        """
        return program

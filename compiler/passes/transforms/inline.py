from compiler.data_structures import Program
from compiler.passes.transforms.bs_transform import BSTransform
from compiler.data_structures.ir import *

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
        for func_name, function in program.functions.items():
            for block in function['blocks'].values():
                for jmps in block.jumps:
                    if type(jmps) == Call:
                        #inline the function:
                        jmps = Jump(program.functions[jmps.name]
                        for inline_block in program.functions[jmps.name]['blocks']:
                            print(type(function[jmps.name]['blocks']))
                            function['blocks'] += (inline_block)



        return program

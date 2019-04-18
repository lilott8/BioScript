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

                #TODO: I assume call is always the last element
                #may or may not be true...
                call = block.get_call()
                if call != None:
                    func_name = call.name
                    print(type(program.functions[func_name]['entry']))
                    print(type(program.functions[func_name]['blocks']))
                    block.instructions[-1] = Label('bob')
                #    if type(jmps) == Call:
                #        #inline the function:
                #print(jmps.name)
                #        #jmps = Jump(program.functions[jmps.name])
                #        for block in program.functions[func_name]['blocks']:
                            
                #        #print(program.symbol_table.functions[jmps.name])
                #        #Efor inline_block in 
                #j        #    print(type(function[jmps.name]['blocks']))
                #        #    function['blocks'] += (inline_block)



        return program

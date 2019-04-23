from compiler.data_structures import Program
from compiler.passes.transforms.bs_transform import BSTransform
from compiler.data_structures.ir import *
from compiler.data_structures.variable import Variable

class Inline(BSTransform):

    def __init__(self):
        super().__init__("inliner")
        self.var_num = 0


    def rename(self, name):
        s = name + str(self.var_num)
        self.var_num = self.var_num + 1
        return s

    def handle_call(self, program, call):

        def inline_var_names(a, parameter_map, global_vars):
            '''
            small local function for transforming parameter arguments into their
            appropriate outer scope variables
            '''
            if a[:-1] in parameter_map: 
                return parameter_map[a[:-1]]

            if a in parameter_map: 
                return parameter_map[a]

            if a in global_vars:
                return a

            return a



        func_name = call.name
        ret = call.defs.name
        func_info = program.symbol_table.functions[func_name]
        global_vars = program.symbol_table.globals.keys()
        parameter_map = {}
        instructions = []

        #map the parameters to the actual variable names
        for arg, uses in zip(func_info.args, call.uses):
            key = arg.name 
            value = uses.name
            #print('KEY VALUE', key, value)
            parameter_map[key] = value 

        for block in program.functions[func_name]['blocks'].values():
            for instr in block.instructions:
                if type(instr) == Dispose:
                    a = inline_var_names(instr.uses[0].name, parameter_map, global_vars)
                    instr.uses[0].name = a
                elif type(instr) == Mix:
                    r = inline_var_names(instr.defs.name, parameter_map, global_vars)
                    a   = inline_var_names(instr.uses[0].name, parameter_map, global_vars)
                    b   = inline_var_names(instr.uses[1].name, parameter_map, global_vars)
                    instr.defs.name = r
                    instr.uses[0].name = a
                    instr.uses[1].name = b
                elif type(instr) == Split:
                    r = inline_var_names(instr.defs.name, parameter_map, global_vars)
                    a = inline_var_names(instr.uses[0].name, parameter_map, global_vars)
                    instr.defs.name = r
                    instr.uses[0].name = a
                elif type(instr) == Detect:
                    r = inline_var_names(instr.defs.name, parameter_map, global_vars)
                    a   = inline_var_names(instr.uses[0].name, global_vars)
                    instr.defs.name = r
                    instr.uses[0] = a
                elif type(instr) == Heat:
                    r = inline_var_names(instr.defs.name, parameter_map, global_vars)
                    a = inline_var_names(instr.uses[0].name, parameter_map, global_vars)
                    instr.defs.name = r
                    instr.uses[0].name = a
                elif type(instr) == Dispense:
                    r = inline_var_names(instr.defs.name, parameter_map, global_vars)
                    a   = inline_var_names(instr.uses[0].name, parameter_map, global_vars)
                    instr.defs.name = r
                    instr.uses[0].name = a
                elif type(instr) == Return:
                    val = inline_var_names(instr.return_value.name, parameter_map, global_vars)
                    r = Variable(ret)
                    a = Temp(Variable(val))
                    #print('temp', a) 
                    instr = Store(r, a)
                    #print(instr)
                elif type(instr) == Call:
                    if instr.name != func_name:
                        instructions = instructions + self.handle_call(program, instr)
                instructions.append(instr)
        return instructions


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
                    ret = call.defs.name  
                    func_name = call.name
                    blocks = program.functions[func_name]['blocks']
                    #get rid of last instruction,
                    block.instructions.pop()
                    block.instructions += self.handle_call(program, call) 

        return program







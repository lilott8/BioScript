from compiler.data_structures import Program
from compiler.passes.transforms.bs_transform import BSTransform
from compiler.data_structures.ir import *
from compiler.data_structures.variable import Variable

class Inline(BSTransform):

    def __init__(self):
        super().__init__("inliner")
        self.var_num = 0


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
            return '{}_{}{}'.format(call.name, a, str(self.var_num))

        
        func_name = call.name
        ret = call.defs.name
        func_info = program.symbol_table.functions[func_name]
        global_vars = program.symbol_table.globals.keys()
        parameter_map = {}
        instructions = []

        #map the return value to the local variable
        for block in program.functions[func_name]['blocks'].values():
            ret_names = block.get_returns()
            if ret_names != None:
                key = ret_names.return_value.name
                value = ret
                parameter_map[key] = value


        #map the parameters to the actual variable names
        for arg, uses in zip(func_info.args, call.uses):
            key = arg.name 
            value = uses.name
            parameter_map[key] = value 


        for block in program.functions[func_name]['blocks'].values():
            for instr in block.instructions:

                inline_instr = None

                if type(instr) == Dispose:
                    a = inline_var_names(instr.uses[0].name, parameter_map, global_vars)
                    inline_instr = Dispose(Variable(a))
                elif type(instr) == Mix:
                    r = inline_var_names(instr.defs.name, parameter_map, global_vars)
                    a   = inline_var_names(instr.uses[0].name, parameter_map, global_vars)
                    b   = inline_var_names(instr.uses[1].name, parameter_map, global_vars)
                    inline_instr = Mix(Variable(r), Variable(a), Variable(b))
                elif type(instr) == Split:
                    r = inline_var_names(instr.defs.name, parameter_map, global_vars)
                    a = inline_var_names(instr.uses[0].name, parameter_map, global_vars)
                    inline_instr = Split(Variable(r), Variable(a))
                elif type(instr) == Detect:
                    r = inline_var_names(instr.defs.name, parameter_map, global_vars)
                    a   = inline_var_names(instr.uses[0].name, global_vars)
                    inline_instr = Detect(Variable(r), instr.module, Variable(a))
                elif type(instr) == Heat:
                    r = inline_var_names(instr.defs.name, parameter_map, global_vars)
                    a = inline_var_names(instr.uses[0].name, parameter_map, global_vars)
                    inline_instr = Heat(Variable(r), Variable(a))
                elif type(instr) == Dispense:
                    r = inline_var_names(instr.defs.name, parameter_map, global_vars)
                    a   = inline_var_names(instr.uses[0].name, parameter_map, global_vars)
                    inline_instr = Dispense(Variable(r), Variable(a))
                elif type(instr) == Return:
                    inline_instr = NOP()
                elif type(instr) == Call:
                    if instr.name != func_name:
                        instructions = instructions + self.handle_call(program, instr)
                        inline_instr = NOP()
                    else:
                        #we have entered a recursive area, cannot inline
                        ret = inline_var_names(instr.defs.name, parameter_map, global_vars)
                        arguments = map(lambda a: Variable(inline_var_names(a.name, parameter_map, global_vars)), instr.uses)
                        inline_instr = Call(Variable(ret), instr.function, arguments)

                instructions.append(inline_instr)
       
        self.var_num = self.var_num + 1 
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

        for block in program.functions['main']['blocks'].values():
            #TODO: I assume call is always the last element
            #may or may not be true...
            call = block.get_call()
            if call != None:
                ret = call.defs.name  
                func_name = call.name
                blocks = program.functions[func_name]['blocks']
                #get rid of last instruction, replace with inline code.
                block.instructions[-1] = NOP()
                block.instructions = block.instructions + self.handle_call(program, call)

        return program







from compiler.data_structures import Program
from compiler.passes.transforms.bs_transform import BSTransform
from compiler.data_structures.ir import *
from compiler.data_structures.variable import *


class Inline(BSTransform):

    def __init__(self):
        super().__init__("inliner")
        self.var_num = 0

    def handle_call(self, program, call, already_called=set()):
        def inline_var_names(a, parameter_map=dict(), global_vars=dict()):
            '''
            small local function for transforming parameter arguments into their
            appropriate outer scope variables
            '''
            if a in global_vars:
                return a

            if a[:-1] in parameter_map:
                return parameter_map[a[:-1]]

            if a in parameter_map:
                return parameter_map[a]

            return a
            # return '{}_{}{}'.format(call.name, a, str(self.var_num))

        func_name = call.name
        ret = call.defs['name']
        func_info = program.symbol_table.functions[func_name]
        global_vars = program.symbol_table.globals.keys()
        parameter_map = {}
        instructions = []

        # map the return value to the local variable
        for block in program.functions[func_name]['blocks'].values():
            ret_names = block.get_returns()
            if ret_names != None:
                key = ret_names.return_value['name']
                value = ret
                parameter_map[key] = value

        # map the parameters to the actual variable names
        for arg, uses in zip(func_info.args, call.uses):
            key = arg
            value = uses['name']
            parameter_map[key] = value 

        for block in program.functions[func_name]['blocks'].values():
            for instr in block.instructions:

                inline_instr = None
                returned_instructions = []

                if type(instr) == Dispose:
                    a = inline_var_names(instr.uses[0]['name'], parameter_map, global_vars)
                    inline_instr = deepcopy(instr)
                    inline_instr.uses[0]['name'] = a
                elif type(instr) == Mix:
                    r = inline_var_names(instr.defs['name'], parameter_map, global_vars)
                    a   = inline_var_names(instr.uses[0]['name'], parameter_map, global_vars)
                    b   = inline_var_names(instr.uses[1]['name'], parameter_map, global_vars)
                    inline_instr = deepcopy(instr)
                    inline_instr.defs['name'] = r
                    inline_instr.uses[0]['name'] = a
                    inline_instr.uses[1]['name'] = b
                elif type(instr) == Split:
                    r = inline_var_names(instr.defs['name'], parameter_map, global_vars)
                    a = inline_var_names(instr.uses[0]['name'], parameter_map, global_vars)
                    inline_instr = deepcopy(instr)
                    inline_instr.defs['name'] = r
                    inline_instr.uses[0]['name'] = a
                elif type(instr) == Detect:
                    r = inline_var_names(instr.defs['name'], parameter_map, global_vars)
                    a = inline_var_names(instr.uses[0]['name'], global_vars=global_vars)
                    inline_instr = deepcopy(instr)
                    inline_instr.defs['name'] = r
                    inline_instr.uses[0]['name'] = a
                elif type(instr) == Heat:
                    r = inline_var_names(instr.defs['name'], parameter_map, global_vars)
                    a = inline_var_names(instr.uses[0]['name'], parameter_map, global_vars)
                    inline_instr = deepcopy(instr)
                    inline_instr.defs['name'] = r
                    inline_instr.uses[0]['name'] = a
                elif type(instr) == Dispense:
                    r = inline_var_names(instr.defs['name'], parameter_map, global_vars)
                    a   = inline_var_names(instr.uses[0]['name'], parameter_map, global_vars)
                    inline_instr = deepcopy(instr)
                    inline_instr.defs['name'] = r
                    inline_instr.uses[0]['name'] = a
                elif type(instr) == Return:
                    inline_instr = None
                elif type(instr) == Call:
                    if instr.name != func_name and instr.name not in already_called:
                        returned_instructions = self.handle_call(program, instr, already_called=already_called|{func_name}) #
                        instructions = instructions + returned_instructions
                        inline_instr = None
                    else:
                        #we have entered a recursive area, cannot inline
                        self.log.warning("target inlining detected recursion. Not currently implemented.")
                        #exit(-1)

                        #old methods
                        #ret = inline_var_names(instr.defs['name'], parameter_map, global_vars)
                        #arguments = map(lambda a: Variable(inline_var_names(a.name, parameter_map, global_vars)), instr.uses)
                        #inline_instr = Call(Variable(ret), instr.function, arguments)

                if inline_instr is not None:
                    instructions.append(inline_instr)
                # New method to allow for inlining time optimization,as we no longer need to do nested call chains after we do one once
                if type(instr) == Call:
                    block.instructions.pop() #pop the call instruction
                    block.instructions = block.instructions + deepcopy(returned_instructions) #append returned instructions
                    # After we remove the call, we directly insert the nested instructions
                    # so future calls to this function don't have to call any other functions at all

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

        # TODO need to check if calls are part of recursive call chain before inlining.
        #   for now, output warning that inlining only works when there are _no_ recursive calls
        self.log.warning(f"Inlining option does not currently check for recursive calls --- use at your own risk!")

        for block in program.functions['main']['blocks'].values():
            #new method that can handle multiple function calls and potential instructions before, after, or between those calls
            if block.label.label != 'main': #inlining only needs to deal with the main
                continue
            final_block = deepcopy(block)
            final_block.instructions = []
            regular_instructions = []
            for internal_blocks in program.functions['main']['blocks'].values():
                for instruc in internal_blocks.instructions: #method to add instructions for calls and regular instructions
                    if type(instruc) == Call:
                        final_block.instructions = final_block.instructions + regular_instructions + self.handle_call(program, instruc)
                        regular_instructions = []
                    else:
                        instru_to_append = deepcopy(instruc)
                        regular_instructions.append(instru_to_append)

            block.instructions = final_block.instructions + regular_instructions

        return program







from compiler.targets.base_target import BaseTarget
from chemicals.chemtypes import ChemTypes
from compiler.data_structures.variable import *
from compiler.data_structures.ir import *

class PuddleTarget(BaseTarget):

    def __init__(self, program, inline=False):
        super().__init__(program, "PuddleTarget", inline)


    def construct_basic_block_code(self, instructions, is_main=False):
        tabs = '  ' if is_main==True else '    '
        code = ''
        for instr in instructions:
            if type(instr) == Dispose:
                code += '{}output({})\n'.format(tabs, instr.uses[0].name)
            elif type(instr) == Mix:
                code += '{}{} = session.mix({}, {})\n'.format(tabs,
                                            instr.defs.name, 
                                            instr.uses[0].name, 
                                            instr.uses[1].name) 
                                            
            elif type(instr) == Split:
                code += '{}{} = session.split({})\n'.format(tabs, instr.defs.name, instr.uses[0].name)
            elif type(instr) == Detect: 
                code += '{}{} = session.detect({}, {})\n'.format(tabs, instr.defs.name, instr.module.name, instr.uses[0].name)
            elif type(instr) == Heat: 
                code += '{}{} = session.heat({}, temp={}, seconds={})\n'.format(tabs, instr.defs.name, instr.uses[0].name, instr.uses[0].size, instr.uses[0].size) 
            elif type(instr) == Dispense:
                code += '{}{} = session.input({}, location=(), volume=1000000.0, dimensions=(1,1))\n'.format(tabs, instr.defs.name, instr.uses[0].name)
            elif type(instr) == Return:
            
                if type(instr.return_value) == Chemical:
                    code += '{}return {}\n'.format(tabs,instr.return_value.name)
                elif type(instr.return_value) == RenamedVar:
                    code += '{}return {}\n'.format(tabs,instr.return_value.name)
                elif type(instr.return_value) == Number: 
                    code += '{}return {}\n'.format(tabs,instr.return_value.value)
            elif type(instr) == Store:
                pass 
            elif type(instr) == Call:
                if inline == True:
                    pass
                else:
                    args = ''
                    for arg in instr.uses:
                        if args:
                            args += ', '+arg.name
                        else:
                            args = arg.name

                    code += '{}{} = {}({});\n'.format(tabs, instr.defs.name, instr.name, args)
            elif type(instr) == BinaryOps:
                pass
            else:
                pass
        return code 


    def transform(self):
        file_name = 'cool_looking_json_file.json'
        self.compiled = 'from puddle import mk_session, project_path\n' \
                        'arch_path = project_path(\'{}\')\n' \
                        'with mk_session(arch_path) as session:\n'.format(file_name)
        #go through the globals and add module/manifest code.
        #i don't exactly know if this is right...
        for name, v in self.program.symbol_table.globals.items():
            if ChemTypes.MAT in v.types:
                self.compiled += '  {} = session.input(location=(), volume=1000000.0, dimensions=(1,1))\n'.format(name)
            #TODO: nothing for module???
            #elif ChemTypes.MODULE in v.types:
            #    self.compiled += '  {} = session.create(None, 1e7, (1, 1))\n'.format(name)

        self.compiled += '\n\n  ##functions:\n'

        for func_name, function in self.program.functions.items():
            if func_name != 'main':
                func_info = self.program.symbol_table.functions[func_name]
                args = '' 
                for arg in func_info.args:
                    var_name = arg.name
                    if args:
                        args += ', {}0'.format(var_name)
                    else:
                        args = '{}0'.format(var_name)

                self.compiled += '  def {}({}):\n'.format(func_name, args)
            else:
                self.compiled += '  ##instructions:\n'

            for block in function['blocks'].values(): 
                is_main = func_name == 'main' 
                self.compiled += self.construct_basic_block_code(block.instructions, is_main=is_main)
            self.compiled += '\n\n'

        print(self.compiled)
        return False

    def write_mix(self) -> str:
        pass

    def write_split(self) -> str:
        pass

    def write_detect(self) -> str:
        pass

    def write_dispose(self) -> str:
        pass

    def write_dispense(self) -> str:
        pass

    def write_expression(self) -> str:
        pass

    def write_branch(self) -> str:
        pass

from compiler.targets.base_target import BaseTarget
from chemicals.chemtypes import ChemTypes
from compiler.data_structures.variable import *
from compiler.data_structures.ir import *

class PuddleTarget(BaseTarget):

    def __init__(self, program, inline=False):
        super().__init__(program, "PuddleTarget", inline)

    def construct_basic_block_code(self, instructions, is_main=False, inline=False):
        tabs = if is_main '  ' else '    ' 
        code = ''
        for instr in instructions:
            



    def transform(self):
        INLINE = False

        #TODO: I have no idea how to do the 'mat' 'module' stuff in puddle...
        self.compiled = 'from puddle import mk_session, project_path\n' \
                        'arch_path = project_path(\'cool_looking_json_file.json\')\n' \
                        'with mk_session(arch_path) as session:\n'
        if INLINE == True:
            pass
        else:
            
            #go through the globals and add module/manifest code.
            #i don't exactly know if this is right...
            for name, v in self.program.symbol_table.globals.items():
                if ChemTypes.MAT in v.types:
                    self.compiled += '  {} = session.create(None, 1e7, (1, 1))\n'.format(name)
                elif ChemTypes.MODULE in v.types:
                    self.compiled += '  {} = session.create(None, 1e7, (1, 1))\n'.format(name)


            for func_name, function in self.program.functions.items():
                if func_name != 'main':
                    func_info = self.program.symbol_table.functions[func_name]
                    args = '' 
                    for arg in func_info.args:
                        var_name = arg.name
                        if args:
                            args += ', {}'.format(var_name)
                        else:
                            args = '{}'.format(var_name)

                    self.compiled += '  def {}({}):\n    pass\n'.format(func_name, args)

                for block in function['blocks'].values(): 
                    pass




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

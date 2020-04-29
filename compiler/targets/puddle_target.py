from compiler.data_structures.ir import *
from compiler.data_structures.writable import Writable
from compiler.targets.base_target import BaseTarget
from chemicals.chemtypes import ChemTypes


class PuddleTarget(BaseTarget):

    def __init__(self, program):
        super().__init__(program, "PuddleTarget")
        self._tab = 0

    @property
    def tab(self):
        return '    ' * self._tab

    def increment_tab(self):
        self._tab += 1

    def decrement_tab(self):
        if self._tab >= 1:
            self._tab -= 1
        else:
            self._tab = 0

    def write_basic_block(self, instructions: List) -> str:
        self.increment_tab()
        code = ""
        for instr in instructions:
            self.log.info(instr)
            if instr.op == IRInstruction.DISPENSE:
                for x in range(0, instr.defs['size']):
                    code += f"{self.tab}{instr.defs['name']}{x} = session.input('{instr.uses[0]['name']}', volume=1.0, dimensions=(1,1))\n"
            elif instr.op == IRInstruction.MIX:
                for x in range(0, instr.defs['size']):
                    code += f"{self.tab}{instr.defs['name']}{x} = session.mix({instr.uses[0]['name']}{x}, " \
                            f"{instr.uses[1]['name']}{x})\n"
            elif instr.op == IRInstruction.HEAT:
                for x in range(0, instr.defs['size']):
                    code += f"{self.tab}{instr.defs['name']}{x} = session.heat({instr.defs['name']}{x}, " \
                            f"temp={instr.meta[0].quantity}, seconds={instr.meta[1].quantity})\n"
            else:
                code += f"#{instr}\n"


        return code

    def construct_basic_block_code(self, instructions, is_main=False):
        tabs = '  ' if is_main else '    '
        code = ''
        for instr in instructions:
            self.log.info(instr)
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
                print(instr)
                code += '{}{} = session.heat({}, temp={}, seconds={})\n'.format(tabs, instr.defs.name, instr.uses[0].name, instr.uses[0].size, instr.uses[0].size) 
            elif type(instr) == Dispense:
                code += f"{tabs}{instr.defs['name']} = session.input({instr.uses['name']}, location=(), volume=1000000.0, dimensions=(1,1))\n"
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
                        'arch_path = project_path("tests/arches/purpledrop.yaml")\n' \
                        'with mk_session(arch_path) as session:\n'
        # for name, v in self.program.symbol_table.globals.items():
        #     if ChemTypes.MAT in v.types:
        #         self.compiled += '  {} = session.input(location=(), volume=1000000.0, dimensions=(1,1))\n'.format(name)
        #     TODO: nothing for module???
            #elif ChemTypes.MODULE in v.types:
            #    self.compiled += '  {} = session.create(None, 1e7, (1, 1))\n'.format(name)

        self.compiled += '    pass\n\n  ##functions:\n'

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
                self.compiled += self.write_basic_block(block.instructions)
                # self.compiled += self.construct_basic_block_code(block.instructions, is_main=is_main)
            self.compiled += '\n\n'

        self.program.write[self.program.name] = Writable(self.program.name,
                                                         "{}/{}.py".format(self.config.output, self.program.name),
                                                         self.compiled)
        if self.config.debug and not self.config.write_out:
            self.log.debug(self.compiled)

        return True

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

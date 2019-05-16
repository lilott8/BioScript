# from compiler.data_structures import Program
from compiler.targets.base_target import BaseTarget
from chemicals.chemtypes import ChemTypes
from compiler.data_structures.variable import *
from compiler.data_structures.ir import *



class ClangTarget(BaseTarget):

    def __init__(self, config, program: 'Program'):
        super().__init__(config, program, "ClangTarget")
        # This *should* be moved into the LLVM target...
        self.keywords = ('alignas', 'alignof', 'and', 'and_eq', 'asm', 'atomic_cancel', 'atomic_commit',
                         'atomic_noexcept', 'auto', 'bitand', 'bitor', 'bool', 'break', 'case', 'catch', 'char',
                         'char16_t', 'char32_t', 'class', 'compl', 'concept', 'const', 'constexpr', 'const_cast',
                         'continue', 'co_await', 'co_return', 'co_yield', 'decltype', 'default', 'delete', 'do',
                         'double', 'dynamic_cast', 'else', 'enum', 'explicit', 'export', 'extern', 'false', 'float',
                         'for', 'friend', 'goto', 'if', 'import', 'inline', 'int', 'long', 'module', 'mutable',
                         'namespace', 'new', 'noexcept', 'not', 'not_eq', 'nullptr', 'operator', 'or', 'or_eq',
                         'private', 'protected', 'public', 'reflexpr', 'register', 'reinterpret_cast', 'requires',
                         'return', 'short', 'signed', 'sizeof', 'static', 'static_assert', 'static_cast', 'struct',
                         'switch', 'synchronized', 'template', 'this', 'thread_local', 'throw', 'true', 'try',
                         'typedef', 'typeid', 'typename', 'union', 'unsigned', 'using', 'virtual', 'void', 'volatile',
                         'wchar_t', 'while', 'xor', 'xor_eq')


    def check_identifier(self, name):
        if name in self.keywords:
            return '{}{}'.format(name, name)
        else:
            return name

    @staticmethod
    def get_type_string(types : ChemTypes):
        '''
        Go through all the types in the set of return types,
        and determine the C++ equivalent of those types
        ''' 
        if ChemTypes.REAL in types:
            return 'double'
        elif ChemTypes.NAT in types:
            return 'double'
        elif ChemTypes.BOOL in types:
            return 'bool'
        elif ChemTypes.CONST in types:
            #don't know what to do here
            assert(False)
        elif ChemTypes.NULL in types or ChemTypes.UNKNOWN in types:
            #unknown type
            #
            return 'None'
        else:
            return 'mat'


    def construct_basic_block_code(self, instructions):
        code = ''
        for instr in instructions:
            if type(instr) == Dispose:
                code += '  dispose({});\n'.format(instr.uses[0].name)
            elif type(instr) == Store:
                #print(instr)
                
                code += '  {} = {};\n'.format(instr.defs.name, instr.uses)
            elif type(instr) == Mix:
                code += '  mat {} = mix({}, {}, {}, {}, {});\n'.format(
                                            instr.defs.name, 
                                            instr.uses[0].name, 
                                            instr.uses[0].size, 
                                            instr.uses[1].name, 
                                            instr.uses[1].size,
                                            1000)  
            elif type(instr) == Split:
                # Using instr.size to show the size it will be splitting into.
                        code += '  mat {} = split({}, {});\n'.format(
                                            instr.defs.name,
                                            instr.uses[0].name,
                                            instr.size)
            elif type(instr) == Detect: 
                        code += '  double {} = detect({}, {}, {});\n'.format(instr.defs.name, instr.module.name, instr.uses[0].name, instr.module.size)
            elif type(instr) == Heat: 
                #(Daniel) I don't know what to fill in for temp or time...
                code += '  mat {} = heat({}, {}, {});\n'.format(instr.defs.name, instr.uses[0].name, instr.uses[0].size, instr.uses[0].size) 
            elif type(instr) == Dispense:
                        code += '  mat {} = dispense({}, {});\n'.format(instr.defs.name, instr.uses[0].name, instr.uses[0].size) 
            elif type(instr) == Return:
            
                if type(instr.return_value) == Chemical:
                    code += '  return {};\n'.format(instr.return_value.name)
                elif type(instr.return_value) == RenamedVar:
                    code += '  return {};\n'.format(instr.return_value.name)
                elif type(instr.return_value) == Number: 
                    code += '  return {};\n'.format(instr.return_value.value)
            elif type(instr) == Call:
                ret = ClangTarget.get_type_string(instr.function.types)
                args = ''
                for arg in instr.uses:
                    if args:
                        args += ', '+arg.name
                    else:
                        args = arg.name
                code += '  {} {} = {}({});\n'.format(ret, instr.defs.name, instr.name, args)
            elif type(instr) == BinaryOps:
                pass
            else:
                pass
        return code


    def transform(self):
        self.function_code = []
        self.compiled = \
        '#include <unistd.h>\n' \
        '#include <vector>\n\n' \
        'struct mat {double quantity;};\n' \
        'struct splitMat{mat values[100];};\n' \
        'struct module{int x, y;};\n\n' \
        'mat mix(mat input1, double input1_quantity, mat input2, double input2_quantity, double quantity) {\n' \
        '  mat output;\n' \
        '  output.quantity = input1.quantity + input2.quantity;\n' \
        '  input1.quantity -= input1_quantity;\n' \
        '  input2.quantity -= input2_quantity;\n' \
        '  sleep(quantity);\n' \
        '  return output;\n' \
        '}\n\n' \
        'std::vector<mat> split(mat input, int quantity) {\n' \
        '  std::vector<mat> output;\n' \
        '  for (int x =0; x < quantity; x++) {\n' \
        '    output[x] = input;\n' \
        '    output[x].quantity = input.quantity/(float)quantity;\n' \
        '  }\n' \
        '  return output;\n' \
        '}\n\n' \
        'mat heat(mat input, double temp, double time) {\n' \
        '  sleep(time);\n' \
        '  return input;\n' \
        '}\n\n'\
        'double detect(module detect, mat input, double quantity) {\n' \
        '  sleep(quantity);\n' \
        '  mat output = input;\n' \
        '  output.quantity = quantity;\n' \
        '  return input;\n' \
        '}\n\n' \
        'void dispose(mat a) {\n\n'\
        '}\n\n' \
        'void drain(mat input) {\n\n' \
        '}\n\n'

        #go through the globals and add module/manifest code.
        for name, v in self.program.symbol_table.globals.items():
            if ChemTypes.MAT in v.types:
                self.compiled += '{} {};\n'.format('mat', name)
            elif ChemTypes.MODULE in v.types:
                self.compiled += '{} {};\n'.format('module', name)
        self.compiled += '\n'

        code_func = []
        for func_name, function in self.program.functions.items():
            code = ''
            if func_name == 'main':
                code = 'int main(int argc, char const **argv) {\n' 
            else:
                func_info = self.program.symbol_table.functions[func_name]
                ret = ClangTarget.get_type_string(func_info.types)
                args = ''

                for arg in func_info.args:
                    var_name = arg.name
                    var_type = ClangTarget.get_type_string(arg.types)
                    if args:
                        args += ', {} {}'.format(var_type, var_name)
                    else:
                        args = '{} {}'.format(var_type, var_name)

                self.compiled += '{} {}({});\n\n'.format(ret, func_name, args)
                code = '{} {}({}) '.format(ret, func_name, args) + '{\n'
            for block in function['blocks'].values(): 
                code += self.construct_basic_block_code(block.instructions)
            code += '}\n\n'
            code_func.append(code)

        for c in code_func:
            self.compiled += c
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









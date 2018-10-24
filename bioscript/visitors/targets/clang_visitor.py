from bioscript.visitors.targets.target_visitor import TargetVisitor
from grammar.parsers.python.BSParser import BSParser
from shared.bs_exceptions import InvalidOperation
from shared.enums.chemtypes import ChemTypes
from shared.enums.instructions import Instruction
from shared.enums.instructions import InstructionSet


class ClangVisitor(TargetVisitor):

    def __init__(self, symbol_table):
        super().__init__(symbol_table, "ClangVisitor")
        self.compiled = "// BSProgram!" + self.nl
        self.compiled += "#include <unistd.h>" + self.nl
        self.compiled += "#include <vector>" + self.nl
        self.compiled += "{}{}{}".format(self.build_structs(), self.nl, self.build_functions())
        self.repeat_counter = 0

    def visitProgram(self, ctx: BSParser.ProgramContext):
        self.scope_stack.append("main")
        self.visitModuleDeclaration(ctx.moduleDeclaration())
        self.visitManifestDeclaration(ctx.manifestDeclaration())
        self.visitStationaryDeclaration(ctx.stationaryDeclaration())

        for func in ctx.functionDeclaration():
            self.visitFunctionDeclaration(func)

        self.add("int main() {")

        for statement in ctx.statements():
            self.add(self.visitStatements(statement))

        self.add("} // main")

    def visitModuleDeclaration(self, ctx: BSParser.ModuleDeclarationContext):
        for name in ctx.IDENTIFIER():
            self.add("module {};".format(self.check_identifier(name.__str__())))

    def visitManifestDeclaration(self, ctx: BSParser.ManifestDeclarationContext):
        for name in ctx.IDENTIFIER():
            self.add("mat {};".format(self.check_identifier(name.__str__())))

    def visitStationaryDeclaration(self, ctx: BSParser.StationaryDeclarationContext):
        for name in ctx.IDENTIFIER():
            self.add("mat {};".format(self.check_identifier(name.__str__())))
        pass

    def visitFunctionDeclaration(self, ctx: BSParser.FunctionDeclarationContext):
        name = ctx.IDENTIFIER().__str__()
        func = self.symbol_table.functions[name]

        self.scope_stack.append(name)

        if ChemTypes.MAT in func.types:
            output = "mat "
        else:
            output = "double "

        output += "{} (".format(name)
        if func.args:
            for arg in func.args:
                output += "{} {}, ".format(
                    self.get_types(self.symbol_table.get_variable(arg.name, self.scope_stack[-1]).types), arg.name)
            output = output[:-2]
        output += ") {{{}".format(self.nl)

        for statement in ctx.statements():
            output += "{} {}".format(self.visitStatements(statement), self.nl)

        output += "return {};{}".format(self.visitReturnStatement(ctx.returnStatement()), self.nl)
        output += "}} // end {} {}".format(name, self.nl)

        self.add(output)
        self.scope_stack.pop()

    def visitFormalParameters(self, ctx: BSParser.FormalParametersContext):
        return super().visitFormalParameters(ctx)

    def visitFormalParameterList(self, ctx: BSParser.FormalParameterListContext):
        return super().visitFormalParameterList(ctx)

    def visitFormalParameter(self, ctx: BSParser.FormalParameterContext):
        return super().visitFormalParameter(ctx)

    def visitFunctionTyping(self, ctx: BSParser.FunctionTypingContext):
        return super().visitFunctionTyping(ctx)

    def visitReturnStatement(self, ctx: BSParser.ReturnStatementContext):
        return ctx.IDENTIFIER().__str__()

    def visitBlockStatement(self, ctx: BSParser.BlockStatementContext):
        output = ""
        for statement in ctx.statements():
            output += "{}{}".format(self.visitStatements(statement), self.nl)
        return output

    def visitStatements(self, ctx: BSParser.StatementsContext):
        return self.visitChildren(ctx)

    def visitIfStatement(self, ctx: BSParser.IfStatementContext):
        output = "if {} {{{}{}".format(self.visitParExpression(ctx.parExpression()), self.nl,
                                       self.visitBlockStatement(ctx.blockStatement(0)))
        output += self.nl
        output += "}"

        if ctx.ELSE():
            output += "ELSE {{ {}".format(self.nl)
            output += "{} {} }}".format(self.visitBlockStatement(ctx.blockStatement(1)), self.nl)

        return output

    def visitWhileStatement(self, ctx: BSParser.WhileStatementContext):
        output = "while"
        output += self.visitParExpression(ctx.parExpression())
        output += "{{ {}".format(self.nl)
        output += "{} {}".format(self.visitBlockStatement(ctx.blockStatement()), self.nl)
        output += "}}{}".format(self.nl)
        return output

    def visitRepeat(self, ctx: BSParser.RepeatContext):
        output = "while({}_{} >= 0) {{ {}".format("bs_repeat_counter", self.increment_repeat_counter(), self.nl)
        output += self.visitBlockStatement(ctx.blockStatement())
        output += "{}_{}--;{}".format("bs_repeat_counter", self.repeat_counter, self.nl)
        output += "}}{}".format(self.nl)
        self.decrement_repeat_counter()
        return output

    def visitHeat(self, ctx: BSParser.HeatContext):
        variable = self.symbol_table.get_variable(ctx.IDENTIFIER().__str__())
        temp = self.visitTemperatureIdentifier(ctx.temperatureIdentifier())
        time = self.visitTimeIdentifier(ctx.timeIdentifier())
        output = ""
        if variable.size > 1:
            """
            This is a SIMD operation
            """
            for x in range(0, variable.size):
                output += "heat({}.at({}), {}, {});{}".format(
                    variable.name, x, temp['quantity'], time['quantity'], self.nl)
        else:
            """
            This is not a SIMD operation
            """
            output += "heat({}, {}, {});".format(variable.name, temp['quantity'], time['quantity'])
        return output

    def visitDispose(self, ctx: BSParser.DisposeContext):
        variable = self.symbol_table.get_variable(self.check_identifier(ctx.IDENTIFIER().__str__()))
        output = ""
        if variable.size > 1:
            """
            This is a SIMD operation
            """
            for x in range(0, variable.size):
                output += "dispose({}.at({});{}".format(variable.name, x, self.nl)
            output += "{} = nullptr;".format(variable.name)
        else:
            """
            This is not a SIMD operation
            """
            output += "dispose({});{}".format(variable.name, self.nl)
            output += "{} = nullptr;".format(variable.name)
        return output

    def visitParExpression(self, ctx: BSParser.ParExpressionContext):
        return "({})".format(self.visitExpression(ctx.expression()))

    def visitExpressionList(self, ctx: BSParser.ExpressionListContext):
        output = ""
        for expr in ctx.expression():
            output += "{}, ".format(self.visitExpression(expr))
        output = output[:-2]
        return output

    def visitTypeType(self, ctx: BSParser.TypeTypeContext):
        return super().visitTypeType(ctx)

    def visitUnionType(self, ctx: BSParser.UnionTypeContext):
        return super().visitUnionType(ctx)

    def visitTypesList(self, ctx: BSParser.TypesListContext):
        return super().visitTypesList(ctx)

    def visitVariableDeclaration(self, ctx: BSParser.VariableDeclarationContext):
        return super().visitVariableDeclaration(ctx)

    def visitVariableDefinition(self, ctx: BSParser.VariableDefinitionContext):
        name = ctx.IDENTIFIER().__str__()

        operation = self.visitChildren(ctx)

        output = ""

        if 'instruction' in operation:
            if operation['instruction'] not in InstructionSet.instructions:
                raise InvalidOperation("Unknown instruction: {}".format(operation['instruction'].name))
            if operation['instruction'] == Instruction.DISPENSE:
                """
                This has to happen here; a = dispense bbb will always give us a size = 1 and is_simd = False.
                This is because in the visitDispenseStatement() parsing, the variable that will determine
                is_simd will be 'bbb', a global variable of size = 1.  Thus is_simd will always be False.
                In order for Dispense to know if it's a SIMD operation, we must know to what variable
                the dispense is occurring -- as that will tell us if it's a SIMD operation or not.
                """
                operation['is_simd'] = True if self.symbol_table.get_variable(name).size > 1 else False
                operation['size'] = self.symbol_table.get_variable(name).size
            if operation['is_simd']:
                output += self.process_simd(name, operation['instruction'], operation)
            else:
                output += self.process_sisd(name, operation['instruction'], operation)
        else:
            output += "// Removing math operations{}".format(self.nl)
            output += "// {} = {}; {}".format(name, operation, self.nl)
        return output

    def visitPrimitiveType(self, ctx: BSParser.PrimitiveTypeContext):
        return super().visitPrimitiveType(ctx)

    def get_types(self, types):
        if ChemTypes.MAT in types:
            return "mat"
        else:
            return "double"

    def build_structs(self):
        output = "struct mat {double quantity;};" + self.nl
        output += "struct splitMat{mat values[100];};" + self.nl
        output += "struct module{int x, y;};" + self.nl

        return output

    def build_functions(self):
        output = "mat mix(mat input1, double input1_quantity, mat input2, " \
                 "double input2_quantity, double quantity) {" + self.nl
        output += "mat output;" + self.nl
        output += "output.quantity = input1.quantity + input2.quantity;" + self.nl
        output += "input1.quantity -= input1_quantity;" + self.nl
        output += "input2.quantity -= input2_quantity;" + self.nl
        output += "sleep(quantity);" + self.nl
        output += "return output;" + self.nl
        output += "}}{}{}".format(self.nl, self.nl)

        output += "std::vector<mat> split(mat input, int quantity) {" + self.nl
        output += "std::vector<mat> output;" + self.nl
        output += "for (int x =0; x < quantity; x++) {" + self.nl
        output += "output.at(x) = input;" + self.nl
        output += "output.at(x).quantity = input.quantity/(float)quantity;" + self.nl
        output += "}" + self.nl
        output += "return output;" + self.nl
        output += "}}{}{}".format(self.nl, self.nl)

        output += "mat heat(mat input, double temp, double time) {" + self.nl
        output += "sleep(time);" + self.nl
        output += "return input;" + self.nl
        output += "}}{}{}".format(self.nl, self.nl)

        output += "double detect(module detect, mat input, double quantity) {" + self.nl
        output += "sleep(quantity);" + self.nl
        output += "return -1.0;" + self.nl
        output += "}}{}{}".format(self.nl, self.nl)

        output += "mat dispense(mat input, double quantity) {" + self.nl
        output += "mat output = input;" + self.nl
        output += "output.quantity = quantity;" + self.nl
        output += "return input;" + self.nl
        output += "}}{}{}".format(self.nl, self.nl)

        output += "void drain(mat input) {" + self.nl
        output += "}}{}{}".format(self.nl, self.nl)

        return output

    def increment_repeat_counter(self):
        temp = self.repeat_counter
        self.repeat_counter += 1
        return temp

    def decrement_repeat_counter(self):
        self.repeat_counter -= 1

    def process_simd(self, lhs: str, op: Instruction, args: dict) -> str:
        output = ""
        if op == Instruction.SPLIT:
            output += "std::vector<mat> {} = split({}, {});{}".format(
                lhs, op['variable'].name, op['size'], self.nl)
        elif op == Instruction.MIX:
            mixes = ""
            for x in args['args']['input']:
                mixes += "{}, {}, ".format(
                    x['variable'].name, x['quantity'])
            # Note the comma between ({} {}) is appended to the first {}!
            output += "std::vector<mat> {} = mix({} {});{}".format(
                lhs, mixes, args['args']['time']['quantity'], self.nl)
        elif op == Instruction.HEAT:
            # Heat is an independent statement.  Meaning it is resolved in the visitHeatStatement()
            pass
        elif op == Instruction.DETECT:
            pass
        elif op == Instruction.METHOD:
            output += "std::vector<mat> {} = {}({});".format(lhs, args['function'].name, args['args']['args'])
        elif op == Instruction.DISPOSE:
            # Dispose is an independent statement.  Meaning it is resolved in the visitDisposeStatement()
            pass
        elif op == Instruction.DISPENSE:
            output += "std::vector<mat> {};{}".format(lhs, self.nl)
            for x in range(0, args['size']):
                output += "{}.at({}) = dispense({},{});{}".format(
                    lhs, x, args['args']['input'], args['args']['quantity'], self.nl)

        return output

    def process_sisd(self, lhs: str, op: Instruction, args: dict) -> str:
        output = ""
        if op == Instruction.SPLIT:
            output += "std::vector<mat> {} = split({}, {});".format(
                lhs, args['args']['input'], args['args']['quantity'])
        elif op == Instruction.MIX:
            mixes = ""
            for x in args['args']['input']:
                mixes += "{}, {}, ".format(
                    x['variable'].name, x['quantity'])
            # Note the comma between ({} {}) is appended to the first {}!
            output += "mat {} = mix({} {});".format(
                lhs, mixes, args['args']['time']['quantity'])
        elif op == Instruction.HEAT:
            # Heat is an independent statement.  Meaning it is resolved in the visitHeatStatement()
            pass
        elif op == Instruction.DETECT:
            output += "float {} = detect({}, {}, {});".format(
                lhs, args['args']['module'], args['args']['input'], args['args']['time']['quantity'])
        elif op == Instruction.METHOD:
            output += "{} {} = {}({});".format(self.get_types(args['function'].types), lhs, args['function'].name,
                                               args['args']['args'])
        elif op == Instruction.DISPOSE:
            # Dispose is an independent statement.  Meaning it is resolved in the visitDisposeStatement()
            pass
        elif op == Instruction.DISPENSE:
            output += "mat {} = dispense({}, {});".format(lhs, args['args']['input'], args['args']['quantity'])
        return output

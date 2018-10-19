from bioscript.visitors.targets.target_visitor import TargetVisitor
from grammar.parsers.python.BSParser import BSParser
from shared.bs_exceptions import InvalidOperation
from shared.bs_exceptions import UndefinedException
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
        # if ctx.dispose():
        #     return self.visitDispose(ctx.dispose())
        # elif ctx.heat():
        #     return self.visitHeat(ctx.heat())
        # elif ctx.ifStatement():
        #     return self.visitIfStatement(ctx.ifStatement())
        # elif ctx.localVariableDeclaration():
        #     return self.visitLocalVariableDeclaration(ctx.localVariableDeclaration())
        # elif ctx.whileStatement():
        #     return self.visitWhileStatement(ctx.whileStatement())
        # elif ctx.repeat():
        #     return self.visitRepeat(ctx.repeat())
        # else:
        #     self.log.fatal("No statement operation: {}".format(ctx.getText()))
        #     return ""

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

    def visitMix(self, ctx: BSParser.MixContext):
        output = "mix("
        inputs = []
        time = {}
        test = set()
        for v in ctx.volumeIdentifier():
            var = self.visit(v)
            inputs.append(var)
            output += "{}, {}, ".format(self.check_identifier(var['variable'].name), var['quantity'])
            test.add(var['variable'].size)
        if len(test) != 1:
            raise InvalidOperation("Trying to run SIMD on unequal array sizes")
        if ctx.timeIdentifier():
            time = self.visitTimeIdentifier(ctx.timeIdentifier())
            output += time['quantity']
        else:
            output += "10.0"
            time['quantity'] = 10.0
            time['unit'] = 's'
        output += ");"
        is_simd = True if next(iter(test)) > 1 else False
        # This will get the first element of the set "test"
        return {'operation': output, 'instruction': Instruction.MIX,
                'args': {'input': inputs, 'time': time}, 'size': next(iter(test)), 'is_simd': is_simd}

    def visitDetect(self, ctx: BSParser.DetectContext):
        output = "detect("
        module = self.check_identifier(ctx.IDENTIFIER(0).__str__())
        material = self.check_identifier(ctx.IDENTIFIER(1).__str__())
        output += "{}, {}, ".format(module, material)
        time = {}
        if ctx.timeIdentifier():
            time = self.visitTimeIdentifier(ctx.timeIdentifier())
            output += "{}".format(time['quantity'])
        else:
            time['quantity'] = 10.0
            time['unit'] = 's'
            output += "10.0"

        output += ");"

        is_simd = True if self.symbol_table.get_variable(material).size > 1 else False
        return {'operation': output, 'instruction': Instruction.DETECT,
                'args': {'input': material, 'module': module, 'time': time},
                'variable': self.symbol_table.get_variable(material),
                'size': self.symbol_table.get_variable(material).size, 'is_simd': is_simd}

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

    def visitSplit(self, ctx: BSParser.SplitContext):
        name = self.check_identifier(ctx.IDENTIFIER().__str__())
        # Split can never be a SIMD operation.
        return {"operation": "split({}, {});".format(name, ctx.INTEGER_LITERAL().__str__()),
                "instruction": Instruction.SPLIT, "size": int(ctx.INTEGER_LITERAL().__str__()),
                'args': {'input': name, "quantity": int(ctx.INTEGER_LITERAL().__str__())},
                'variable': self.symbol_table.get_variable(name), 'is_simd': False}

    def visitDispense(self, ctx: BSParser.DispenseContext):
        """
        Read the comment in visitVariableDeclaration() for further understanding of why
        is_simd = False and size = 1.  In short, the name of the variable in here
        is going to be a global variable and will always be of size = 1
        :param ctx:
        :return:
        """
        name = ctx.IDENTIFIER().__str__()
        return {'operation': "dispense({});".format(name),
                "instruction": Instruction.DISPENSE, 'size': 1,
                'args': {'input': name, 'quantity': 10.0}, 'variable': self.symbol_table.get_variable(name),
                'is_simd': False}

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
            output += "dispose({});".format(variable.name)
        return output
        is_simd = True if self.symbol_table.get_variable(name).size != 1 else False
        return {'operation': "dispense({});".format(name),
                "instruction": Instruction.DISPOSE, 'size': self.symbol_table.get_variable(name).size,
                'args': {'input': name}, 'variable': self.symbol_table.get_variable(name), 'is_simd': is_simd}

    def visitExpression(self, ctx: BSParser.ExpressionContext):
        if ctx.primary():
            return self.visitPrimary(ctx.primary())
        else:
            exp1 = self.visitExpression(ctx.expression(0))
            exp2 = self.visitExpression(ctx.expression(1))
            if ctx.MULTIPLY():
                op = "*"
            elif ctx.DIVIDE():
                op = "/"
            elif ctx.ADDITION():
                op = "+"
            elif ctx.SUBTRACT():
                op = "-"
            elif ctx.AND():
                op = "&&"
            elif ctx.EQUALITY():
                op = "=="
            elif ctx.GT():
                op = ">"
            elif ctx.GTE:
                op = ">="
            elif ctx.LT():
                op = "<"
            elif ctx.LTE():
                op = "<="
            elif ctx.NOTEQUAL():
                op = "!="
            elif ctx.OR():
                op = "||"
            else:
                op = "=="

            if ctx.LBRACKET():
                output = "{}[{}]".format(exp1, exp2)
            else:
                output = "{}{}{}".format(exp1, op, exp2)

            return output

    def visitParExpression(self, ctx: BSParser.ParExpressionContext):
        return "({})".format(self.visitExpression(ctx.expression()))

    def visitMethodCall(self, ctx: BSParser.MethodCallContext):
        operation = "{}(".format(ctx.IDENTIFIER().__str__())
        arguments = ""
        method = self.symbol_table.functions[ctx.IDENTIFIER().__str__()]
        if ctx.expressionList():
            operation += "{}".format(self.visitExpressionList(ctx.expressionList()))
            arguments = "{}".format(self.visitExpressionList(ctx.expressionList()))
        operation += ");"
        is_simd = True if method.return_size > 1 else False
        return {'operation': operation, 'instruction': Instruction.METHOD,
                'args': {'args': arguments}, 'size': method.return_size, 'function': method, 'is_simd': is_simd}

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
                This is because in the visitDispenseStatement() parsing, the variable that will determing
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

    def visitPrimary(self, ctx: BSParser.PrimaryContext):
        if ctx.IDENTIFIER():
            if not self.symbol_table.get_variable(ctx.IDENTIFIER().__str__()):
                raise UndefinedException("Undeclared variable: {}".format(ctx.IDENTIFIER().__str__()))
            return ctx.IDENTIFIER().__str__()
        elif ctx.literal():
            return self.visitLiteral(ctx.literal())
        else:
            return self.visitExpression(ctx.expression())

    def visitLiteral(self, ctx: BSParser.LiteralContext):
        if ctx.INTEGER_LITERAL():
            return ctx.INTEGER_LITERAL().__str__()
        elif ctx.BOOL_LITERAL():
            return ctx.BOOL_LITERAL().__str__()
        elif ctx.FLOAT_LITERAL():
            return ctx.FLOAT_LITERAL().__str__()
        else:
            return ctx.STRING_LITERAL().__str__()

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
            output += "heat({}, {}, {});".format(args['args']['input'], args['args']['temp'], args['args']['quantity'])
        elif op == Instruction.DETECT:
            output += "float {} = detect({}, {}, {});".format(
                lhs, args['args']['module'], args['args']['input'], args['args']['time']['quantity'])
        elif op == Instruction.METHOD:
            output += "{} {} = {}({});".format(args['size'], lhs, args['args']['function'].name, args['args']['args'])
        elif op == Instruction.DISPOSE:
            output += "dispose({}, {});{}".format(lhs, args['args'][''], args['args'][''])
        elif op == Instruction.DISPENSE:
            output += "mat {} = dispense({}, {});".format(lhs, args['args']['input'], args['args']['quantity'])
        return output

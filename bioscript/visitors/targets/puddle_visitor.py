from bioscript.visitors.targets.target_visitor import TargetVisitor
from grammar.parsers.python.BSParser import BSParser
from shared.bs_exceptions import *
from shared.enums.instructions import Instruction
from shared.enums.instructions import InstructionSet


class PuddleVisitor(TargetVisitor):

    def __init__(self, symbol_table):
        super().__init__(symbol_table, "PuddleVisitor")
        self.tab_count = 0
        self.tab = "\t"
        detectors = {'heat', 'volume'}

    def increment_tab(self):
        self.tab += "\t"
        self.tab_count += 1

    def decrement_tab(self):
        self.tab = ""
        self.tab_count -= 1

        if self.tab_count < 0:
            self.tab_count = 0

        for x in range(0, self.tab_count):
            self.tab += "\t"

    def visitProgram(self, ctx: BSParser.ProgramContext):
        self.scope_stack.append("main")

        output = "from puddle import mk_session, project_path {}".format(self.nl)

        output += 'arch_path = project_path("{}"){}'.format('PUT SOMETHING HERE', self.nl)
        output += 'with mk_session(arch_path) as session:{}'.format(self.nl)

        # output += "{}".format(self.visitManifestDeclaration(ctx.manifestDeclaration()))

        for i in ctx.statements():
            output += self.visitStatements(i)

        self.compiled = self.nl + output

    def visitModuleDeclaration(self, ctx: BSParser.ModuleDeclarationContext):
        return super().visitModuleDeclaration(ctx)

    def visitManifestDeclaration(self, ctx: BSParser.ManifestDeclarationContext):
        output = ""
        for manifest in ctx.IDENTIFIER():
            name = manifest.__str__()
            output += '{}{} = session.input(location=(), volume=1000000.0, dimensions=(1,1)){}'.format(self.tab, name,
                                                                                                       self.nl)
        return output

    def visitStationaryDeclaration(self, ctx: BSParser.StationaryDeclarationContext):
        return super().visitStationaryDeclaration(ctx)

    def visitFunctionDeclaration(self, ctx: BSParser.FunctionDeclarationContext):
        return super().visitFunctionDeclaration(ctx)

    def visitFormalParameters(self, ctx: BSParser.FormalParametersContext):
        return super().visitFormalParameters(ctx)

    def visitFormalParameterList(self, ctx: BSParser.FormalParameterListContext):
        return super().visitFormalParameterList(ctx)

    def visitFormalParameter(self, ctx: BSParser.FormalParameterContext):
        return super().visitFormalParameter(ctx)

    def visitFunctionTyping(self, ctx: BSParser.FunctionTypingContext):
        return super().visitFunctionTyping(ctx)

    def visitReturnStatement(self, ctx: BSParser.ReturnStatementContext):
        return super().visitReturnStatement(ctx)

    def visitBlockStatement(self, ctx: BSParser.BlockStatementContext):
        output = ""
        for x in ctx.statements():
            output += "{}{}".format(self.visitStatements(x), self.nl)
        return output

    def visitStatements(self, ctx: BSParser.StatementsContext):
        return self.visitChildren(ctx)

    def visitIfStatement(self, ctx: BSParser.IfStatementContext):
        output = ""
        # Build the if condition....
        condition = self.visitParExpression(ctx.parExpression())
        output += "{}if {}:{}".format(self.tab, condition, self.nl)
        # Increment the tab
        self.increment_tab()
        # Visit the statements
        output += self.visitBlockStatement(ctx.blockStatement(0))
        self.decrement_tab()

        if ctx.ELSE():
            output += "{}else:{}".format(self.tab, self.nl)
            self.increment_tab()
            output += self.visitBlockStatement(ctx.blockStatement(1))
            self.decrement_tab()

        return output

    def visitWhileStatement(self, ctx: BSParser.WhileStatementContext):
        output = ""

        condition = self.visitParExpression(ctx.parExpression())
        output += "{}while {}:{}".format(self.tab, condition, self.nl)
        self.increment_tab()
        output += self.visitBlockStatement(ctx.blockStatement())
        self.decrement_tab()

        return output

    def visitRepeat(self, ctx: BSParser.RepeatContext):
        output = ""

        value = int(ctx.INTEGER_LITERAL().__str__())
        output += "{}while {}>0:{}".format(self.tab, value, self.nl)
        self.increment_tab()
        output += self.visitBlockStatement(ctx.blockStatement())
        self.decrement_tab()

        return output

    def visitHeat(self, ctx: BSParser.HeatContext):
        variable = self.symbol_table.get_variable(ctx.IDENTIFIER().__str__())
        temp = self.visitTemperatureIdentifier(ctx.temperatureIdentifier())
        time = self.visitTimeIdentifier(ctx.timeIdentifier())

        output = ""
        if variable.size > 1:
            """
            This is a SIMD operation.
            """
            for x in range(0, variable.size):
                output += "{}{}{} = heat({}{}, {})".format(
                    self.tab, variable.name, x, variable.name, x, temp['quantity'])
                inputs = []
                outputs = []
                # name = "{}{}".format(variable.name, x)
                # inputs.append(MFSimVarBuilder.build_general_input(Variable(name, set())))
                # inputs.append(MFSimVarBuilder.build_temperature_property(temp['quantity'], temp['units']))
                # # Add time property.
                # if ctx.timeIdentifier():
                #     inputs.append(MFSimVarBuilder.build_time_property(time['quantity'], time['units']))
                # output.append(MFSimVarBuilder.build_operation('HEAT', 'getInstructionId()', 'HEAT', inputs, outputs))
        else:
            """
            This is not a SIMD operation.
            """
            output += "{}{} = session.heat({},temp={},seconds={})".format(
                self.tab, variable.name, variable.name, temp['quantity'], time['quantity'])
            self.log.info(output)
        return output

    def visitDispose(self, ctx: BSParser.DisposeContext):
        variable = self.symbol_table.get_variable(ctx.IDENTIFIER().__str__())
        output = ""
        if variable.size > 1:
            """
            This is a SIMD operation.
            """
            for x in range(0, variable.size):
                output += "{}output({}{})".format(self.tab, variable.name, x)
        else:
            """
            This is not a SIMD operation.
            """
            output += "{}output({})".format(self.tab, variable.name)
        return output

    def visitParExpression(self, ctx: BSParser.ParExpressionContext):
        return "({})".format(self.visitExpression(ctx.expression()))

    def visitMethodCall(self, ctx: BSParser.MethodCallContext):
        return super().visitMethodCall(ctx)

    def visitExpressionList(self, ctx: BSParser.ExpressionListContext):
        return super().visitExpressionList(ctx)

    def visitVariableDeclaration(self, ctx: BSParser.VariableDeclarationContext):
        return self.visitChildren(ctx)

    def visitVariableDefinition(self, ctx: BSParser.VariableDefinitionContext):
        name = ctx.IDENTIFIER().__str__()
        # Get the inputs...
        op = self.visitChildren(ctx)

        output = ""
        if 'instruction' in op:
            if op['instruction'] not in InstructionSet.instructions:
                raise InvalidOperation("Unknown instruction: {}".format(op['op'].name))
            if op['instruction'] == Instruction.DISPENSE:
                """
                This has to happen here; a = dispense bbb will always give us a size = 1 and is_simd = False.
                This is because in the visitDispenseStatement() parsing, the variable that will determine
                is_simd will be 'bbb', a global variable of size = 1.  Thus is_simd will always be False.
                In order for Dispense to know if it's a SIMD operation, we must know to what variable
                the dispense is occurring -- as that will tell us if it's a SIMD operation or not.
                """
                op['is_simd'] = True if self.symbol_table.get_variable(name).size > 1 else False
                op['size'] = self.symbol_table.get_variable(name).size
            if op['is_simd']:
                output = self.process_simd(name, op['instruction'], op)
            else:
                output = self.process_sisd(name, op['instruction'], op)
        else:
            output += "{}{} = {}".format(self.tab, name, op)
        return output + self.nl

    def process_simd(self, lhs: str, op: Instruction, args: dict) -> dict:
        output = ""
        self.log.info(args)

        if op == Instruction.SPLIT:
            pass
        elif op == Instruction.MIX:
            pass
        elif op == Instruction.HEAT:
            pass
        elif op == Instruction.DETECT:
            pass
        elif op == Instruction.METHOD:
            pass
        elif op == Instruction.DISPOSE:
            pass
        elif op == Instruction.DISPENSE:
            for x in range(0, args['size']):
                name = '{}_{}'.format(lhs, x)
                output += '{}{} = session.input({}, location=(), volume=1000000.0, dimensions=(1,1)){}'.format(
                    self.tab, name, args['args']['input'], self.nl)
        return output

    def process_sisd(self, lhs: str, op: Instruction, args: dict) -> dict:
        output = ""
        if op == Instruction.SPLIT:
            output += self.build_split(lhs, args['args']['input'], args['args']['quantity'])
            #output += "std::vector<mat> {} = split({}, {});".format(
            #    lhs, args['args']['input'], args['args']['quantity'])
        elif op == Instruction.MIX:
            mixes = ""
            for x in args['args']['input']:
                mixes += "{}, ".format(x['variable'].name)
            # Note the comma between ({} {}) is appended to the first {}!
            output += "{}{} = mix({})".format(self.tab, lhs, mixes[:-1])
        elif op == Instruction.HEAT:
            # Heat is an independent statement.  Meaning it is resolved in the visitHeatStatement()
            pass
        elif op == Instruction.DETECT:
            # args['args']['time']['quantity'] is the time component.
            output += "{}{} = detect({}, {})".format(
                self.tab, lhs, args['args']['module'], args['args']['input'])
        elif op == Instruction.METHOD:
            output += "{}{} = {}({});".format(self.tab, lhs, args['function'].name,
                                              args['args']['args'])
            raise InvalidOperation("Not implemented yet")
        elif op == Instruction.DISPOSE:
            # Dispose is an independent statement.  Meaning it is resolved in the visitDisposeStatement()
            pass
        elif op == Instruction.DISPENSE:
            output += "{}{} = sessions.input({}, volume={})".format(
                self.tab, lhs, args['args']['input'], args['args']['quantity'])
        return output

    def build_split(self, lhs: str, operand: str, size: int)-> str:
        if size == 2:
            pass
        else:
            return self.build_split_recursive(lhs, 1, size)

    def build_split_recursive(self, lhs, count, max):
        output = "{}{}{}, {} = split({})".format(self.tab, lhs, count, count*2, lhs)
        if count < max:
            self.build_split_recursive(lhs, count*2, max)
        return output


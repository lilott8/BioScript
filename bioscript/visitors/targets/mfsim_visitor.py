import json

import pyperclip

from bioscript.visitors.targets.target_visitor import TargetVisitor
from grammar.parsers.python.BSParser import BSParser
from shared.bs_exceptions import *
from shared.enums.instructions import Instruction
from shared.enums.instructions import InstructionSet
from shared.variable import Variable


class MFSimVisitor(TargetVisitor):

    def __init__(self, symbol_table):
        super().__init__(symbol_table, "MFSimVisitor")
        self.open = "{"
        self.close = "}"
        self.compiled = {}

    def get_tab(self):
        pass

    def visitProgram(self, ctx: BSParser.ProgramContext):
        self.scope_stack.append("main")

        self.compiled['EXPERIMENT'] = {
            'NAME': self.config.input_file,
            'INPUTS': [],
            'INSTRUCTIONS': []
        }

        self.compiled['EXPERIMENT']['INPUTS'] = self.visitManifestDeclaration(ctx.manifestDeclaration())
        self.compiled['EXPERIMENT']['INPUTS'] += self.visitStationaryDeclaration(ctx.stationaryDeclaration())
        self.compiled['EXPERIMENT']['INPUTS'] += self.visitModuleDeclaration(ctx.moduleDeclaration())

        for statement in ctx.statements():
            self.compiled['EXPERIMENT']['INSTRUCTIONS'].append(self.visitStatements(statement))

        self.log.warning("You are copying things to the clipboard")
        pyperclip.copy(json.dumps(self.compiled))

    def visitModuleDeclaration(self, ctx: BSParser.ModuleDeclarationContext):
        output = []
        for module in ctx.IDENTIFIER():
            output = []
            variable = {"VARIABLE_DECLARATION": {"ID": module.__str__(), "NAME": module.__str__(), "TYPE": "SENSOR"}}
            output.append(variable)

        return output

    def visitManifestDeclaration(self, ctx: BSParser.ManifestDeclarationContext):
        output = []
        for manifest in ctx.IDENTIFIER():
            variable = {
                "VARIABLE_DECLARATION": {"ID": manifest.__str__(), "NAME": manifest.__str__(), "TYPE": "CHEMICAL"}}
            output.append(variable)

        return output

    def visitStationaryDeclaration(self, ctx: BSParser.StationaryDeclarationContext):
        output = []
        for manifest in ctx.IDENTIFIER():
            variable = {
                "VARIABLE_DECLARATION": {"ID": manifest.__str__(), "NAME": manifest.__str__(), "TYPE": "STATIONARY"}}
            output.append(variable)

        return output

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
        output = []
        for x in ctx.statements():
            output.append(self.visitStatements(x))
        return output

    def visitStatements(self, ctx: BSParser.StatementsContext):
        return self.visitChildren(ctx)

    def visitIfStatement(self, ctx: BSParser.IfStatementContext):
        output = dict()
        output['OPERATION'] = {'NAME': 'IF', 'ID': 'getInstructionID()',
                               'CLASSIFICATION': 'CFG_BRANCH', 'CONDITION': "", 'TRUE_BRANCH': []}
        output['OPERATION']["CONDITION"] = self.visitParExpression(ctx.parExpression())
        output['OPERATION']["TRUE_BRANCH"] = self.visitBlockStatement(ctx.blockStatement(0))

        if ctx.ELSE():
            output['OPERATION']['FALSE_BRANCH'] = []
            output['OPERATION']['FALSE_BRANCH'] = self.visitBlockStatement(ctx.blockStatement(1))

        return output

    def visitWhileStatement(self, ctx: BSParser.WhileStatementContext):
        raise UnsupportedOperation("MFSim doesn't support WHILE loops.")

    def visitRepeat(self, ctx: BSParser.RepeatContext):
        output = dict()
        output['OPERATION'] = {'NAME': 'REPEAT', 'ID': 'getInstructionID()',
                               'CLASSIFICATION': 'CFG_LOOP',
                               'LOOP_NUM': int(ctx.INTEGER_LITERAL().__str__()),
                               'OPERATIONS': []}
        output['OPERATION']['OPERATIONS'] = self.visitBlockStatement(ctx.blockStatement())
        return output

    def visitHeat(self, ctx: BSParser.HeatContext):
        variable = self.symbol_table.get_variable(ctx.IDENTIFIER().__str__())
        temp = self.visitTemperatureIdentifier(ctx.temperatureIdentifier())
        time = self.visitTimeIdentifier(ctx.timeIdentifier())
        output = dict()
        output['OPERATION'] = {'NAME': 'HEAT',
                               'ID': 'getInstructionID()',
                               'CLASSIFICATION': "HEAT",
                               'INPUTS': [], 'OUTPUTS': []}

        if variable.size > 1:
            """
            This is a SIMD operation.
            """
            for x in range(0, variable.size):
                output += "# Add simd operation"
        else:
            """
            This is not a SIMD operation.
            """
            inputs = dict()
            # Add variable.
            inputs['INPUT_TYPE'] = 'VARIABLE'
            inputs['VARIABLE'] = {'NAME': variable.name}
            output['OPERATION']['INPUTS'].append(inputs)
            # Add temperature property.
            inputs = dict()
            inputs['INPUT_TYPE'] = 'PROPERTY'
            inputs['TEMPERATURE'] = {'VALUE': temp['quantity'], 'UNITS': temp['units'].name}
            output['OPERATION']['INPUTS'].append(inputs)
            # Add time property.
            if ctx.timeIdentifier():
                inputs = dict()
                inputs['INPUT_TYPE'] = 'PROPERTY'
                inputs['TIME'] = {'VALUE': time['quantity'], 'UNITS': time['units'].name}
                output['OPERATION']['INPUTS'].append(inputs)

        return output

    def visitDispose(self, ctx: BSParser.DisposeContext):
        output = dict()
        output['OPERATION'] = {'NAME': 'dispose',
                               'ID': 'getInstructionID()',
                               'CLASSIFICATION': 'OUTPUT',
                               'INPUTS': [], 'OUTPUTS': []}
        variable = self.symbol_table.get_variable(ctx.IDENTIFIER().__str__())
        if variable.size == 1:
            output['OPERATION']['INPUTS'].append({'INPUT_TYPE': 'VARIABLE', 'VARIABLE': {'NAME': variable.name}})
        else:
            self.log.warning("Dispose simd semantics not built.")
        return output

    def visitParExpression(self, ctx: BSParser.ParExpressionContext):
        return "({})".format(self.visitExpression(ctx.expression()))

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
                output += self.process_simd(name, op['instruction'], op)
            else:
                output = self.process_sisd(name, op['instruction'], op)
        return output

    def visitPrimary(self, ctx: BSParser.PrimaryContext):
        return super().visitPrimary(ctx)

    def visitLiteral(self, ctx: BSParser.LiteralContext):
        return super().visitLiteral(ctx)

    def process_simd(self, lhs: str, op: Instruction, args: dict) -> dict:
        output = ""

        return output

    def process_sisd(self, lhs: str, op: Instruction, args: dict) -> dict:
        output = dict()
        output['OPERATION'] = dict()
        output['OPERATION']['INPUTS'] = []
        output['OPERATION']['OUTPUTS'] = []
        output['OPERATION']['ID'] = "getInstructionID()"

        if 'time' in args['args']:
            output['OPERATION']['INPUTS'].append(self.build_property('TIME', args['args']['time']))

        if op == Instruction.SPLIT:
            output['OPERATION']['NAME'] = 'SPLIT'
            output['OPERATION']['CLASSIFICATION'] = 'SPLIT'

            if args['variable'].is_stationary:
                output['OPERATION']['INPUTS'].append(self.stationary_variable(args['variable']))
            else:
                output['OPERATION']['INPUTS'].append(self.mobile_variable(args['variable'], {}))

            for x in range(0, args['size']):
                name = "{}{}".format(lhs, x)
                output['OPERATION']['OUTPUTS'].append(self.mobile_variable(Variable(name), {}))
            pass
        elif op == Instruction.MIX:
            output['OPERATION']['NAME'] = 'MIX'
            output['OPERATION']['CLASSIFICATION'] = 'MIX'

            for x in args['args']['input']:
                mixes = dict()
                if x['variable'].is_stationary:
                    mixes = self.stationary_variable(x['variable'])
                else:
                    mixes = self.mobile_variable(x['variable'], x)
                output['OPERATION']['INPUTS'].append(mixes)

            output['OPERATION']['OUTPUTS'].append(
                {'VARIABLE_DECLARATION': {'ID': lhs, 'TYPE': 'VARIABLE', 'NAME': lhs}})
        elif op == Instruction.HEAT:
            # Heat is an independent statement.  Meaning it is resolved in the visitHeatStatement()
            pass
        elif op == Instruction.DETECT:
            output['OPERATION']['NAME'] = 'DETECT'
            output['OPERATION']['CLASSIFICATION'] = 'DETECT'
            if args['variable'].is_stationary:
                output['OPERATION']['INPUTS'] += self.stationary_variable(args['variable'])
            else:
                output['OPERATION']['INPUTS'].append(self.mobile_variable(args['variable'], {}))

            declaration = dict()
            declaration['SENSOR_DECLARATION'] = {'ID': lhs, 'NAME': lhs, 'TYPE': 'SENSOR'}
            output['OPERATION']['OUTPUTS'].append(declaration)
        elif op == Instruction.METHOD:
            self.log.critical("Alpha-convert this trash!")
            pass
        elif op == Instruction.DISPOSE:
            # Dispose is an independent statement.  Meaning it is resolved in the visitDisposeStatement()
            pass
        elif op == Instruction.DISPENSE:
            output['OPERATION']['NAME'] = 'DISPENSE'
            output['OPERATION']['CLASSIFICATION'] = 'DISPENSE'
            output['OPERATION']['INPUTS'].append(self.mobile_variable(args['variable'], args))
            output['OPERATION']['OUTPUTS'].append(
                {'VARIABLE_DECLARATION': {'ID': lhs, 'NAME': lhs, 'TYPE': 'VARIABLE'}})

        return output

    def stationary_variable(self, variable: Variable) -> dict:
        output = dict()
        output['INPUT_TYPE'] = 'VARIABLE'
        output['STATIONARY'] = {'NAME': variable.name}
        return output

    def mobile_variable(self, variable: Variable, volume: dict) -> dict:
        output = dict()
        output['INPUT_TYPE'] = 'VARIABLE'
        output['CHEMICAL'] = {'VARIABLE': {'NAME': variable.name}}
        if 'quantity' in volume:
            output['VOLUME'] = {'VALUE': volume['quantity'], 'UNITS': volume['units'].name}
        return output

    def build_property(self, property_type: str, values: dict) -> dict:
        prop = dict()
        prop['INPUT_TYPE'] = 'PROPERTY'
        prop[property_type.upper()] = {'VALUE': values['quantity'], 'UNITS': values['units'].name}
        return prop

import json

import pyperclip

from bioscript.visitors.targets.target_visitor import TargetVisitor
from grammar.parsers.python.BSParser import BSParser
from shared.bs_exceptions import InvalidOperation
from shared.enums.instructions import Instruction
from shared.enums.instructions import InstructionSet


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
        return self.visitChildren(ctx)

    def visitStatements(self, ctx: BSParser.StatementsContext):
        return self.visitChildren(ctx)

    def visitIfStatement(self, ctx: BSParser.IfStatementContext):
        output = dict()
        output["NAME"] = "IF"
        output["ID"] = "getInstructionID()"
        output["CLASSIFICATION"] = "CFG_BRANCH"
        output["CONDITION"] = self.visitParExpression(ctx.parExpression())
        output["TRUE_BRANCH"] = self.visitBlockStatement(ctx.blockStatement(0))

        if ctx.ELSE():
            output['FALSE_BRANCH'] = self.visitBlockStatement(ctx.blockStatement(1))

        return output

    def visitWhileStatement(self, ctx: BSParser.WhileStatementContext):
        return super().visitWhileStatement(ctx)

    def visitRepeat(self, ctx: BSParser.RepeatContext):
        return super().visitRepeat(ctx)

    def visitHeat(self, ctx: BSParser.HeatContext):
        variable = self.symbol_table.get_variable(ctx.IDENTIFIER().__str__())
        temp = self.visitTemperatureIdentifier(ctx.temperatureIdentifier())
        time = self.visitTimeIdentifier(ctx.timeIdentifier())
        self.log.info(time)
        output = dict()
        output['OPERATION'] = {'NAME': 'HEAT',
                               'ID': 'getNextInstructionID()',
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

    def visitParExpression(self, ctx: BSParser.ParExpressionContext):
        return self.visitChildren(ctx)

    def visitExpressionList(self, ctx: BSParser.ExpressionListContext):
        return super().visitExpressionList(ctx)

    def visitVariableDeclaration(self, ctx: BSParser.VariableDeclarationContext):
        return self.visitChildren(ctx)

    def visitVariableDefinition(self, ctx: BSParser.VariableDefinitionContext):
        name = ctx.IDENTIFIER().__str__()
        # Get the inputs...
        op = self.visitChildren(ctx)
        self.log.info(op)

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

        if op == Instruction.SPLIT:
            output['OPERATION']['NAME'] = 'SPLIT'
            output['OPERATION']['CLASSIFICATION'] = 'SPLIT'
            pass
        elif op == Instruction.MIX:
            output['OPERATION']['NAME'] = 'MIX'
            output['OPERATION']['CLASSIFICATION'] = 'MIX'

            for x in args['args']['input']:
                mixes = dict()
                mixes['INPUT_TYPE'] = 'VARIABLE'
                mixes['CHEMICAL'] = dict()
                mixes['CHEMICAL']['VARIABLE'] = dict()
                mixes['CHEMICAL']['VARIABLE']['NAME'] = x['variable'].name
                mixes['VOLUME'] = dict()
                mixes['VOLUME']['VALUE'] = x['quantity']
                mixes['VOLUME']['UNITS'] = x['units'].name
                output['OPERATION']['INPUTS'].append(mixes)
            if 'time' in args['args']['time']:
                prop = dict()
                prop['INPUT_TYPE'] = "PROPERTY"
                prop['TIME'] = dict()
                prop['TIME']['VALUE'] = args['time']['quantity']
                prop['TIME']['UNITS'] = args['time']['units'].name
        elif op == Instruction.HEAT:
            pass
        elif op == Instruction.DETECT:
            output['OPERATION']['NAME'] = 'DETECT'
            output['OPERATION']['CLASSIFICATION'] = 'DETECT'
            pass
        elif op == Instruction.METHOD:
            pass
        elif op == Instruction.DISPOSE:
            pass
        elif op == Instruction.DISPENSE:
            output['OPERATION']['NAME'] = 'DISPENSE'
            output['OPERATION']['CLASSIFICATION'] = 'DISPENSE'
            pass

        return output

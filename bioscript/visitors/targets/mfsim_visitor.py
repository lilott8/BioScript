import copy
import json

import pyperclip

from bioscript.builders.mfsim_builder import MFSimVarBuilder
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
            instructions = self.visitStatements(statement)
            if len(instructions) > 1:
                """
                SIMD's need to be extended because 
                they are an array of instructions.
                """
                self.compiled['EXPERIMENT']['INSTRUCTIONS'].extend(instructions)
            else:
                self.compiled['EXPERIMENT']['INSTRUCTIONS'].append(instructions)

        self.log.warning("You are copying things to the clipboard")
        pyperclip.copy(json.dumps(self.compiled))

    def visitModuleDeclaration(self, ctx: BSParser.ModuleDeclarationContext):
        output = []
        for module in ctx.IDENTIFIER():
            output.append(MFSimVarBuilder.build_sensor_variable(module.__str__(), module.__str__()))
        return output

    def visitManifestDeclaration(self, ctx: BSParser.ManifestDeclarationContext):
        output = []
        for manifest in ctx.IDENTIFIER():
            output.append(MFSimVarBuilder.build_global_variable(manifest.__str__(), manifest.__str__(), "CHEMICAL"))
        return output

    def visitStationaryDeclaration(self, ctx: BSParser.StationaryDeclarationContext):
        output = []
        for manifest in ctx.IDENTIFIER():
            output.append(MFSimVarBuilder.build_global_variable(manifest.__str__(), manifest.__str__(), "STATIONARY"))
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
        true_branch = self.visitBlockStatement(ctx.blockStatement(0))

        false_branch = list()
        if ctx.ELSE():
            false_branch = self.visitBlockStatement(ctx.blockStatement(1))

        return MFSimVarBuilder.build_if_operation('IF', 'getInstructionID()',
                                                  self.visitParExpression(ctx.parExpression()),
                                                  true_branch, false_branch)

    def visitWhileStatement(self, ctx: BSParser.WhileStatementContext):
        raise UnsupportedOperation("MFSim doesn't support WHILE loops.")

    def visitRepeat(self, ctx: BSParser.RepeatContext):
        return MFSimVarBuilder.build_repeat_statement('REPEAT', 'getInstructionId()',
                                                      int(ctx.INTEGER_LITERAL().__str__()),
                                                      self.visitBlockStatement(ctx.blockStatement()))

    def visitHeat(self, ctx: BSParser.HeatContext):
        variable = self.symbol_table.get_variable(ctx.IDENTIFIER().__str__())
        temp = self.visitTemperatureIdentifier(ctx.temperatureIdentifier())
        time = self.visitTimeIdentifier(ctx.timeIdentifier())

        output = []
        inputs = []
        outputs = []
        if variable.size > 1:
            """
            This is a SIMD operation.
            """
            for x in range(0, variable.size):
                inputs = []
                outputs = []
                name = "{}{}".format(variable.name, x)
                inputs.append(MFSimVarBuilder.build_general_input(Variable(name, set())))
                inputs.append(MFSimVarBuilder.build_temperature_property(temp['quantity'], temp['units']))
                # Add time property.
                if ctx.timeIdentifier():
                    inputs.append(MFSimVarBuilder.build_time_property(time['quantity'], time['units']))
                output.append(MFSimVarBuilder.build_operation('HEAT', 'getInstructionId()', 'HEAT', inputs, outputs))
        else:
            """
            This is not a SIMD operation.
            """
            # Add variable.
            inputs.append(MFSimVarBuilder.build_general_input(variable))
            inputs.append(MFSimVarBuilder.build_temperature_property(temp['quantity'], temp['units']))
            # Add time property.
            if ctx.timeIdentifier():
                inputs.append(MFSimVarBuilder.build_time_property(time['quantity'], time['units']))
            output.append(MFSimVarBuilder.build_operation('HEAT', 'getInstructionID()', 'HEAT', inputs, outputs))
        return output

    def visitDispose(self, ctx: BSParser.DisposeContext):
        variable = self.symbol_table.get_variable(ctx.IDENTIFIER().__str__())
        output = list()
        if variable.size == 1:
            output.append(MFSimVarBuilder.build_operation(
                'DISPOSE', 'getInstructionID()', 'DISPOSE', [MFSimVarBuilder.build_general_input(
                    variable)], []))
        else:
            for x in range(0, variable.size):
                name = "{}{}".format(variable.name, x)
                output.append(MFSimVarBuilder.build_operation(
                    'DISPOSE', 'getInstructionID()', 'DISPOSE', [MFSimVarBuilder.build_general_input(
                        Variable(name, set()))], []))
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
                output = self.process_simd(name, op['instruction'], op)
            else:
                output = self.process_sisd(name, op['instruction'], op)
        return output

    def visitPrimary(self, ctx: BSParser.PrimaryContext):
        return super().visitPrimary(ctx)

    def visitLiteral(self, ctx: BSParser.LiteralContext):
        return super().visitLiteral(ctx)

    def process_simd(self, lhs: str, op: Instruction, args: dict) -> list:
        output = []
        inputs = []
        outputs = []

        if op == Instruction.SPLIT:
            self.log.error("Not doing anything with split, right now.")
            pass
        elif op == Instruction.MIX:
            """
            If either of the inputs are globals, 
            then we must build the dispense for it.
            """
            var = None
            if args['args']['input'][0]['variable'].is_global:
                var = args['args']['input'][0]['variable']
            if args['args']['input'][1]['variable'].is_global:
                var = args['args']['input'][1]['variable']

            if var is not None:
                for x in range(0, args['size']):
                    id_outputs = list()
                    # id_inputs.append(MFSimVarBuilder.build_input_with_volume(args['args']['inputs'][index])
                    id_outputs.append(MFSimVarBuilder.build_variable_declaration("{}{}".format(var.name, x),
                                                                                 "{}{}".format(var.name, x)))
                    id_inputs = [MFSimVarBuilder.build_variable_declaration("{}{}".format(var.name, x),
                                                                            "{}{}".format(var.name, x))]
                    output.append(MFSimVarBuilder.build_operation("DISPENSE", 'getInstructionID()', 'DISPENSE',
                                                                  id_inputs, []))
            for x in range(0, args['size']):
                output_name = "{}{}".format(lhs, x)
                inputs = []
                mix_output = MFSimVarBuilder.build_variable_declaration(output_name, output_name)
                for v in args['args']['input']:
                    # This is deepcopy, because we don't want to affect
                    # the symbol table's representation of the variable.
                    simd_var = copy.deepcopy(v['variable'])
                    simd_var.name = "{}{}".format(simd_var.name, x)
                    if simd_var.is_stationary:
                        inputs.append(MFSimVarBuilder.build_stationary_input(simd_var))
                    else:
                        inputs.append(MFSimVarBuilder.build_input_with_volume(simd_var, v))
                output.append(MFSimVarBuilder.build_operation('MIX', 'getInstructionID()', 'MIX', inputs, mix_output))
        elif op == Instruction.HEAT:
            # Heat is an independent statement.  Meaning it is resolved in the visitHeatStatement()
            pass
        elif op == Instruction.DETECT:
            for x in range(0, args['size']):
                inputs = list()
                outputs = list()
                simd_var = copy.deepcopy(args['variable'])
                simd_var.name = "{}{}".format(simd_var.name, x)
                if simd_var.is_stationary:
                    inputs.append(MFSimVarBuilder.build_stationary_input(simd_var))
                else:
                    inputs.append(MFSimVarBuilder.build_general_input(simd_var))
                outputs.append(MFSimVarBuilder.build_detect_output(lhs, lhs))
                output.append(
                    MFSimVarBuilder.build_operation("DETECT", 'getInstructionID()', 'DETECT', inputs, outputs))
            pass
        elif op == Instruction.METHOD:
            self.log.critical("Alpha-convert this trash!")
            pass
        elif op == Instruction.DISPOSE:
            # Dispose is an independent statement.  Meaning it is resolved in the visitDisposeStatement()
            pass
        elif op == Instruction.DISPENSE:
            for x in range(0, args['size']):
                name = '{}{}'.format(args['args']['input'], x)
                dispense_input = MFSimVarBuilder.build_variable_declaration(name, name)
                output.append(MFSimVarBuilder.build_operation("DISPENSE", 'getInstructionID()', "DISPENSE",
                                                              [dispense_input], []))
        return output

    def process_sisd(self, lhs: str, op: Instruction, args: dict) -> dict:
        inputs = []
        outputs = []
        output = dict()

        if 'time' in args['args']:
            inputs.append(MFSimVarBuilder.build_time_property(args['args']['time']))

        if op == Instruction.SPLIT:
            if args['variable'].is_stationary:
                inputs.append(MFSimVarBuilder.build_stationary_input(args['variable']))
            else:
                inputs.append(MFSimVarBuilder.build_general_input(args['variable']))

            for x in range(0, args['size']):
                name = "{}{}".format(lhs, x)
                outputs.append(MFSimVarBuilder.build_output(-1, name))
            output = MFSimVarBuilder.build_operation('SPLIT', 'getInstructionID()', 'SPLIT', inputs, outputs)
        elif op == Instruction.MIX:
            for x in args['args']['input']:
                if x['variable'].is_stationary:
                    inputs.append(MFSimVarBuilder.build_stationary_input(x['variable']))
                else:
                    inputs.append(MFSimVarBuilder.build_input_with_volume(x['variable'], x))
            outputs.append(MFSimVarBuilder.build_output(lhs, lhs, "VARIABLE"))
            output = MFSimVarBuilder.build_operation('MIX', 'getInstructionID()', 'MIX', inputs, outputs)
        elif op == Instruction.HEAT:
            # Heat is an independent statement.  Meaning it is resolved in the visitHeatStatement()
            pass
        elif op == Instruction.DETECT:
            if args['variable'].is_stationary:
                inputs.append(MFSimVarBuilder.build_stationary_input(args['variable']))
            else:
                inputs.append(MFSimVarBuilder.build_general_input(args['variable']))
            outputs.append(MFSimVarBuilder.build_detect_output(lhs, lhs))
            output = MFSimVarBuilder.build_operation("DETECT", 'getInstructionID()', 'DETECT', inputs, outputs)
        elif op == Instruction.METHOD:
            self.log.critical("Alpha-convert this trash!")
            pass
        elif op == Instruction.DISPOSE:
            # Dispose is an independent statement.  Meaning it is resolved in the visitDisposeStatement()
            pass
        elif op == Instruction.DISPENSE:
            inputs.append(MFSimVarBuilder.build_input_with_volume(args['variable'], args['args']))
            outputs.append(MFSimVarBuilder.build_variable_declaration(lhs, lhs))
            output = MFSimVarBuilder.build_operation('DISPENSE', 'getInstructionID()', 'DISPENSE', inputs, outputs)

        return output

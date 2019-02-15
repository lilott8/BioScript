import random
import string

from compiler.bs_ir import *
from compiler.data_structures.basic_block import BasicBlock
from compiler.semantics.bs_base_visitor import BSBaseVisitor
from grammar.parsers.python.BSParser import BSParser
from shared.enums.instructions import *


class IRVisitor(BSBaseVisitor):

    def __init__(self, symbol_table):
        super().__init__(symbol_table, "Basic Block Visitor")
        self.basic_blocks = list()
        self.current_block = BasicBlock(1)
        self.allocation_map = dict()
        self.globals = dict()
        self.branch_stack = list()

    def visitProgram(self, ctx: BSParser.ProgramContext):
        self.scope_stack.append("main")

        self.visitModuleDeclaration(ctx.moduleDeclaration())
        self.visitManifestDeclaration(ctx.manifestDeclaration())
        self.visitStationaryDeclaration(ctx.stationaryDeclaration())

        if ctx.functionDeclaration():
            for func in ctx.functionDeclaration():
                # Add the chain of basic blocks resulting from the functions.
                # self.visitFunctionDeclaration(func)
                pass

        self.symbol_table.current_scope = self.symbol_table.scope_map['main']

        # Add all the subsequent instructions to the B.B.
        for i in ctx.statements():
            self.visitStatements(i)
        self.basic_blocks.append(self.current_block)

    def visitModuleDeclaration(self, ctx: BSParser.ModuleDeclarationContext):
        for module in ctx.IDENTIFIER():
            name = module.__str__()
            self.globals[name] = Module(self.symbol_table.get_global(name))

    def visitManifestDeclaration(self, ctx: BSParser.ManifestDeclarationContext):
        for manifest in ctx.IDENTIFIER():
            name = manifest.__str__()
            self.globals[name] = Global(self.symbol_table.get_global(name))

    def visitStationaryDeclaration(self, ctx: BSParser.StationaryDeclarationContext):
        for stationary in ctx.IDENTIFIER():
            name = stationary.__str__()
            self.globals[name] = Stationary(self.symbol_table.get_global(name))

    def visitFunctionDeclaration(self, ctx: BSParser.FunctionDeclarationContext):
        name = ctx.IDENTIFIER().__str__()
        func = self.symbol_table.functions[name]

        self.scope_stack.append(name)
        self.symbol_table.current_scope = self.symbol_table.scope_map[name]

        for statement in ctx.statements():
            self.visitStatements(statement)

        self.current_block.add(self.visitReturnStatement(ctx.returnStatement()))

        self.scope_stack.pop()
        return None

    def visitReturnStatement(self, ctx: BSParser.ReturnStatementContext):
        return Return(self.allocation_map[ctx.IDENTIFIER().__str__()], None)

    def visitIfStatement(self, ctx: BSParser.IfStatementContext):
        par_expression = self.visitParExpression(ctx.parExpression())
        if BSBaseVisitor.is_number(par_expression['exp1']):
            exp1 = Constant(float(par_expression['exp1']))
        else:
            exp1 = self.allocation_map[par_expression['exp1']]
        if BSBaseVisitor.is_number(par_expression['exp2']):
            exp2 = Constant(float(par_expression['exp2']))
        else:
            exp2 = self.allocation_map[par_expression['exp2']]

        condition = Conditional(par_expression['op'], exp1, exp2)
        true_block = BasicBlock()
        true_label = Label("bsbbc_{}_t".format(self.current_block.nid))
        true_block.add(true_label)
        condition.true_branch = true_label

        false_block = BasicBlock()
        false_label = Label("bsbbc_{}_f".format(false_block.nid))
        false_block.add(false_label)
        condition.false_branch = false_label

        self.current_block.add(condition)
        self.basic_blocks.append(self.current_block)
        # Set the current block to the true branch.
        self.current_block = true_block
        # Visit the conditional's statements.
        self.visitBlockStatement(ctx.blockStatement(0))

        from_else = False
        if ctx.ELSE():
            self.basic_blocks.append(self.current_block)
            self.current_block = false_block
            self.current_block.add(false_label)
            self.visitBlockStatement(ctx.blockStatement(1))
            from_else = True

        if from_else:
            self.basic_blocks.append(self.current_block)
            # add the join.
            join_block = BasicBlock()
            join_label = Label("bsbb_{}_j".format(join_block.nid))
            join_block.add(join_label)
            self.current_block = join_block
            true_block.add(Jump(join_label))
        else:
            self.current_block.add(Jump(false_label))

        return NOP()

    def visitWhileStatement(self, ctx: BSParser.WhileStatementContext):
        par_expression = self.visitParExpression(ctx.parExpression())

        if BSBaseVisitor.is_number(par_expression['exp1']):
            exp1 = Constant(float(par_expression['exp1']))
        else:
            exp1 = self.allocation_map[par_expression['exp1']]
        if BSBaseVisitor.is_number(par_expression['exp2']):
            exp2 = Constant(float(par_expression['exp2']))
        else:
            exp2 = self.allocation_map[par_expression['exp2']]

        pre_condition_label_string = "bsbbw_{}_l".format(self.current_block.nid)
        pre_condition_label = Label(pre_condition_label_string)
        self.current_block.add(pre_condition_label)

        condition = Conditional(par_expression['op'], exp1, exp2)
        true_block = BasicBlock()
        true_label = Label("bsbbw_{}_t".format(self.current_block.nid))
        true_block.add(true_label)
        condition.true_branch = true_label

        false_block = BasicBlock()
        false_label = Label("bsbbw_{}_f".format(false_block.nid))
        false_block.add(false_label)
        condition.false_branch = false_label

        self.current_block.add(condition)
        self.basic_blocks.append(self.current_block)
        self.current_block = true_block

        self.visitBlockStatement(ctx.blockStatement())
        self.current_block.add(Jump(pre_condition_label))

        self.basic_blocks.append(self.current_block)
        self.current_block = BasicBlock()

        return NOP()

    def visitRepeat(self, ctx: BSParser.RepeatContext):

        # # ir = LoopIR()
        new_var = Number(''.join(random.choices(string.ascii_uppercase + string.digits, k=8)),
                         {ChemTypes.REAL}, self.scope_stack[-1], value=float(ctx.INTEGER_LITERAL().__str__()))

        pre_condition_label_string = "bsbbr_{}_l".format(self.current_block.nid)
        pre_condition_label = Label(pre_condition_label_string)
        self.current_block.add(pre_condition_label)
        condition = Conditional(RelationalOps.GT, Temp(new_var), Constant(0))

        true_block = BasicBlock()
        true_label = Label("bsbbr_{}_t".format(self.current_block.nid))
        true_block.add(true_label)
        condition.true_branch = true_label

        false_block = BasicBlock()
        false_label = Label("bsbbr_{}_f".format(false_block.nid))
        false_block.add(false_label)
        condition.false_branch = false_label

        self.current_block.add(condition)
        self.basic_blocks.append(self.current_block)
        self.current_block = true_block

        self.visitBlockStatement(ctx.blockStatement())
        self.current_block.add(BinaryOp(new_var, Constant(1), BinaryOps.SUBTRACT))
        self.current_block.add(Jump(pre_condition_label))

        self.basic_blocks.append(self.current_block)
        self.current_block = BasicBlock()
        self.current_block.add(false_label)

        return NOP()

    def visitParExpression(self, ctx: BSParser.ParExpressionContext):
        return self.visitExpression(ctx.expression())

    def visitMethodCall(self, ctx: BSParser.MethodCallContext):
        name = ctx.IDENTIFIER().__str__()
        return {"args": self.symbol_table.functions[name].args, "func": self.symbol_table.functions[name],
                "op": IRInstruction.CALL}

    def visitVariableDefinition(self, ctx: BSParser.VariableDefinitionContext):
        details = self.visitChildren(ctx)
        lhs = Temp(self.symbol_table.get_local(ctx.IDENTIFIER().__str__(), self.scope_stack[-1]))
        self.allocation_map[lhs.value.name] = lhs

        if 'op' not in details:
            ir = Store(lhs, Constant(float(details)))
        elif details['op'] == IRInstruction.MIX:
            ir = Mix(lhs, details['reagents'][0], details['reagents'][1], details['execute_for'])
        elif details['op'] == IRInstruction.SPLIT:
            ir = Split(lhs, details['reagents'][0], details['size'])
        elif details['op'] == IRInstruction.DISPENSE:
            ir = Dispense(lhs, details['reagents'][0])
        elif details['op'] == IRInstruction.CALL:
            ir = Store(lhs, Call(details['func']))
        elif details['op'] == IRInstruction.BINARYOP:
            # ir = BinaryOp()
            ir = NOP()
            pass
        else:
            ir = NOP()

        self.current_block.add(ir)
        return ir

    def visitVariableDeclaration(self, ctx: BSParser.VariableDeclarationContext):
        return self.visitChildren(ctx)

    def visitMix(self, ctx: BSParser.MixContext):

        if ctx.timeIdentifier():
            temp_time = self.visitTimeIdentifier(ctx.timeIdentifier())
            time = (temp_time['quantity'], temp_time['units'])
        else:
            time = (10, BSTime.SECOND)

        reagents = [self.allocation_map[self.visitVolumeIdentifier(ctx.volumeIdentifier(0))['variable'].name],
                    self.allocation_map[self.visitVolumeIdentifier(ctx.volumeIdentifier(1))['variable'].name]]

        return {"reagents": reagents, "execute_for": time, "op": IRInstruction.MIX}

    def visitDetect(self, ctx: BSParser.DetectContext):
        module = self.globals[ctx.IDENTIFIER(0).__str__()]
        reagent = [self.allocation_map[ctx.IDENTIFIER(1).__str__()]]

        if ctx.timeIdentifier():
            time = super().visitTimeIdentifier(ctx.timeIdentifier())
        else:
            time = (10, BSTime.SECOND)

        return {"module": module, "reagents": reagent, "execute_for": time, "op": IRInstruction.DETECT}

    def visitHeat(self, ctx: BSParser.HeatContext):
        register = self.allocation_map[ctx.IDENTIFIER().__str__()]
        if ctx.timeIdentifier():
            time = self.visitTimeIdentifier(ctx.timeIdentifier())
        else:
            time = (10, BSTime.SECOND)
        ir = Heat(register, register, time)
        self.current_block.add(ir)
        return ir

    def visitSplit(self, ctx: BSParser.SplitContext):
        reagents = self.allocation_map[ctx.IDENTIFIER().__str__()]
        size = int(ctx.INTEGER_LITERAL().__str__())
        return {"reagents": reagents, "size": size, "op": IRInstruction.SPLIT}

    def visitDispense(self, ctx: BSParser.DispenseContext):
        return {"reagents": [self.symbol_table.get_global(ctx.IDENTIFIER().__str__())], "op": IRInstruction.DISPENSE}

    def visitDispose(self, ctx: BSParser.DisposeContext):
        output = Output(self.symbol_table.get_local(ctx.IDENTIFIER().__str__(), self.scope_stack[-1]))
        ir = Dispose(output, self.allocation_map[output.value.name])
        self.current_block.add(ir)
        return ir

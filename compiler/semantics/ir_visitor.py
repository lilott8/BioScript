import random
import string

import networkx as nx

from compiler.bs_ir import *
from compiler.data_structures.basic_block import BasicBlock
from compiler.semantics.bs_base_visitor import BSBaseVisitor
from grammar.parsers.python.BSParser import BSParser
from shared.enums.instructions import *


class IRVisitor(BSBaseVisitor):

    def __init__(self, symbol_table):
        super().__init__(symbol_table, "Basic Block Visitor")
        self.basic_blocks = dict()
        self.current_block = BasicBlock()
        self.allocation_map = dict()
        self.globals = dict()
        self.control_stack = list()
        self.graph = nx.DiGraph()
        self.graph.add_node(self.current_block.nid)

    def get_ir(self):
        return {"basic_blocks": self.basic_blocks, "globals": self.globals, "cfg": self.graph}

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

        self.basic_blocks[self.current_block.nid] = self.current_block

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
        # Build the conditional for this statement.
        par_expression = self.visitParExpression(ctx.parExpression())
        if BSBaseVisitor.is_number(par_expression['exp1']):
            exp1 = Constant(float(par_expression['exp1']))
        else:
            exp1 = self.allocation_map[par_expression['exp1']]
        if BSBaseVisitor.is_number(par_expression['exp2']):
            exp2 = Constant(float(par_expression['exp2']))
        else:
            exp2 = self.allocation_map[par_expression['exp2']]

        # Build the IR Conditional
        condition = Conditional(par_expression['op'], exp1, exp2)
        # Build the true block of this statement.
        true_block = BasicBlock()
        true_label = Label("bsbbif_{}_t".format(self.current_block.nid))
        true_block.label = true_label
        true_block.add(true_label)
        self.graph.add_node(true_block.nid)
        self.graph.add_edge(self.current_block.nid, true_block.nid)
        condition.true_branch = true_label
        self.basic_blocks[true_block.nid] = true_block

        # Build the false block of this statement.
        false_block = BasicBlock()
        false_label = Label("bsbbif_{}_f".format(false_block.nid))
        false_block.label = false_label
        false_block.add(false_label)
        self.graph.add_node(false_block.nid)
        self.graph.add_edge(self.current_block.nid, false_block.nid)
        condition.false_branch = false_label
        self.basic_blocks[false_block.nid] = false_block

        if not ctx.ELSE():
            join_block = false_block
        else:
            join_block = BasicBlock()
            join_label = Label("bsbbif_{}_j".format(join_block.nid))
            join_block.label = join_label
            self.graph.add_node(join_block.nid)
            self.basic_blocks[join_block.nid] = join_block

        self.current_block.add("Condition")
        self.basic_blocks[self.current_block.nid] = self.current_block
        self.current_block = true_block
        # Save the parent join
        self.control_stack.append(join_block)
        # Visit the conditional's statements.
        self.visitBlockStatement(ctx.blockStatement(0))

        join_block = self.control_stack.pop()

        # This check guarantees that a true block will not jump to a join
        # while dealing with nested conditionals.
        if self.control_stack and len(self.graph.edges(true_block.nid)) == 0:
            true_block.add(Jump(join_block.label))
            self.graph.add_edge(true_block.nid, join_block.nid)
        elif len(self.control_stack) == 0 and len(self.graph.edges(true_block.nid)) == 0:
            true_block.add(Jump(join_block.label))
            self.graph.add_edge(true_block.nid, join_block.nid)

        if ctx.ELSE():
            self.basic_blocks[self.current_block.nid] = self.current_block
            self.control_stack.append(join_block)
            self.current_block = false_block

            self.visitBlockStatement(ctx.blockStatement(1))

            join_block = self.control_stack.pop()
            # This check guarantees that a false block will not jump to a join
            # while dealing with nested conditionals.
            if self.control_stack and len(self.graph.edges(false_block.nid)) == 0:
                false_block.add(Jump(join_block.label))
                self.graph.add_edge(false_block.nid, join_block.nid)
            elif len(self.control_stack) == 0 and len(self.graph.edges(false_block.nid)) == 0:
                false_block.add(Jump(join_block.label))
                self.graph.add_edge(false_block.nid, join_block.nid)

        # Add the current join to the parent join.
        if self.control_stack:
            join_block.add(Jump(self.control_stack[-1].label))
            self.graph.add_edge(join_block.nid, self.control_stack[-1].nid)
            pass

        self.basic_blocks[self.current_block.nid] = self.current_block
        self.current_block = join_block

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

        # Condition is added to self.current_block.
        condition = Conditional(par_expression['op'], exp1, exp2)
        true_block = BasicBlock()
        self.graph.add_node(true_block.nid)
        true_label = Label("bsbbw_{}_t".format(self.current_block.nid))
        true_block.add(true_label)
        self.basic_blocks[true_block.nid] = true_block
        condition.true_branch = true_label

        self.current_block.add(condition)
        # If condition evaluates true.
        self.graph.add_cycle([true_block.nid, self.current_block.nid])
        self.control_stack.append(self.current_block)
        self.basic_blocks[self.current_block] = self.current_block
        self.current_block = true_block

        self.visitBlockStatement(ctx.blockStatement())
        self.current_block.add(Jump(pre_condition_label))

        parent_block = self.control_stack.pop()

        # This is dealing with the false branch. If it's false
        # and we are nested, then the false branch needs an edge
        # to the parent conditional block, not the false block.
        # If the stack is empty, then we move onto the false branch.
        if not self.control_stack:
            # If condition evaluates false.
            false_block = BasicBlock()
            # false_block.add("bsbbw_{}_f".format(false_block.nid))
            self.graph.add_node(false_block.nid)
            false_label = Label("bsbbw_{}_f".format(false_block.nid))
            false_block.add(false_label)
            false_block.label = false_label
            condition.false_branch = false_label
            # Create the edge.
            self.graph.add_edge(parent_block.nid, false_block.nid)
            # We are done, so we need to handle the book keeping for
            # next basic block generation.
            self.basic_blocks[self.current_block.nid] = self.current_block
            self.current_block = false_block
            pass
        else:
            self.graph.add_edge(parent_block.nid, self.control_stack[-1].nid)
            pass

        return NOP()

    def visitRepeat(self, ctx: BSParser.RepeatContext):
        # ir = LoopIR()
        new_var = Number(''.join(random.choices(string.ascii_uppercase + string.digits, k=8)),
                         {ChemTypes.REAL}, self.scope_stack[-1], value=float(ctx.INTEGER_LITERAL().__str__()))

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

        condition = Conditional(RelationalOps.GT, Temp(new_var), Constant(0))
        self.current_block.add(condition)

        # Condition is added to self.current_block.
        condition = Conditional(par_expression['op'], exp1, exp2)
        true_block = BasicBlock()
        self.graph.add_node(true_block.nid)
        true_label = Label("bsbbw_{}_t".format(self.current_block.nid))
        true_block.add(true_label)
        self.basic_blocks[true_block.nid] = true_block
        condition.true_branch = true_label

        # If condition evaluates true.
        self.graph.add_cycle([true_block.nid, self.current_block.nid])
        self.control_stack.append(self.current_block)
        self.basic_blocks[self.current_block] = self.current_block
        self.current_block = true_block

        self.visitBlockStatement(ctx.blockStatement())
        self.current_block.add(Jump(pre_condition_label))

        parent_block = self.control_stack.pop()

        # This is dealing with the false branch. If it's false
        # and we are nested, then the false branch needs an edge
        # to the parent conditional block, not the false block.
        # If the stack is empty, then we move onto the false branch.
        if not self.control_stack:
            # If condition evaluates false.
            false_block = BasicBlock()
            # false_block.add("bsbbw_{}_f".format(false_block.nid))
            self.graph.add_node(false_block.nid)
            false_label = Label("bsbbw_{}_f".format(false_block.nid))
            false_block.add(false_label)
            false_block.label = false_label
            condition.false_branch = false_label
            # Create the edge.
            self.graph.add_edge(parent_block.nid, false_block.nid)
            # We are done, so we need to handle the book keeping for
            # next basic block generation.
            self.basic_blocks[self.current_block.nid] = self.current_block
            self.current_block = false_block
            pass
        else:
            self.graph.add_edge(parent_block.nid, self.control_stack[-1].nid)
            pass

        return NOP()

    def visitParExpression(self, ctx: BSParser.ParExpressionContext):
        return self.visitExpression(ctx.expression())

    def visitMethodCall(self, ctx: BSParser.MethodCallContext):
        name = ctx.IDENTIFIER().__str__()
        return {"args": self.symbol_table.functions[name].args, "func": self.symbol_table.functions[name],
                "op": IRInstruction.CALL}

    def visitVariableDefinition(self, ctx: BSParser.VariableDefinitionContext):
        details = self.visitChildren(ctx)
        lhs = Temp(self.symbol_table.get_local(
            self.increment_rename_var(ctx.IDENTIFIER().__str__()), self.scope_stack[-1]))
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
        elif details['op'] in InstructionSet.BinaryOps:
            ir = BinaryOp(details['exp1'], details['exp2'], details['op'])
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
        output = Output(self.symbol_table.get_local(
            self.get_renamed_var(ctx.IDENTIFIER().__str__()), self.scope_stack[-1]))
        ir = Dispose(output, self.allocation_map[output.value.name])
        self.current_block.add(ir)
        return ir

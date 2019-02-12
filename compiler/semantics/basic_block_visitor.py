import random
import string

from compiler.bs_ir import *
from compiler.data_structures.basic_block import BasicBlock
from compiler.semantics.bs_base_visitor import BSBaseVisitor
from grammar.parsers.python.BSParser import BSParser


class BasicBlockVisitor(BSBaseVisitor):

    def __init__(self, symbol_table):
        super().__init__(symbol_table, "Basic Block Visitor")
        self.basic_blocks = list()
        self.current_block = BasicBlock(1)

    def visitProgram(self, ctx: BSParser.ProgramContext):
        self.scope_stack.append("main")

        if ctx.functionDeclaration():
            for func in ctx.functionDeclaration():
                # Add the chain of basic blocks resulting from the functions.
                # output += "{}{}{}".format(self.visitFunctionDeclaration(func), self.nl, self.nl)
                pass

        self.symbol_table.current_scope = self.symbol_table.scope_map['main']

        # Add all the subsequent instructions to the B.B.
        for i in ctx.statements():
            self.visitStatements(i)
        self.basic_blocks.append(self.current_block)
        x = 1

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
        ir = ReturnIR()
        ir.consumes = self.symbol_table.get_local(ctx.IDENTIFIER().__str__(), self.scope_stack[-1])
        return ir

    def visitIfStatement(self, ctx: BSParser.IfStatementContext):
        ir = BranchIR()
        ir.condition = self.visitParExpression(ctx.parExpression())

        self.current_block.add(ir)
        self.basic_blocks.append(self.current_block)
        self.current_block = BasicBlock()

        self.visitBlockStatement(ctx.blockStatement(0))

        if ctx.ELSE():
            self.basic_blocks.append(self.current_block)
            self.current_block = BasicBlock()
            # Basic Block id it jumps to.
            ir.jumps = -1
            self.visitBlockStatement(ctx.blockStatement(1))
            self.basic_blocks.append(self.current_block)
            self.current_block = BasicBlock()

        return ir

    def visitWhileStatement(self, ctx: BSParser.WhileStatementContext):
        ir = LoopIR()
        ir.condition = self.visitParExpression(ctx.parExpression())

        self.basic_blocks.append(self.current_block)
        self.current_block = BasicBlock()

        self.visitBlockStatement(ctx.blockStatement())

        self.basic_blocks.append(self.current_block)
        self.current_block = BasicBlock()

        return ir

    def visitRepeat(self, ctx: BSParser.RepeatContext):
        ir = LoopIR()
        new_var = ''.join(random.choices(string.ascii_uppercase + string.digits, k=8))

        ir.condition = "{} < {}".format(new_var, ctx.INTEGER_LITERAL().__str__())

        self.basic_blocks.append(ir)
        self.current_block = BasicBlock()

        self.visitBlockStatement(ctx.blockStatement())

        decrement = NumericIR()
        decrement.expression = "{} = {}-1".format(new_var, new_var)
        self.current_block.add(decrement)

        self.basic_blocks.append(self.current_block)
        self.current_block = BasicBlock()

        return None

    def visitMethodCall(self, ctx: BSParser.MethodCallContext):
        ir = MethodIR()
        name = ctx.IDENTIFIER().__str__()
        ir.args = self.symbol_table.functions[name].args
        ir.uses = ir.args
        ir.jumps.append(self.symbol_table.functions[name])

        return ir

    def visitVariableDefinition(self, ctx: BSParser.VariableDefinitionContext):
        ir = self.visitChildren(ctx)
        name = ctx.IDENTIFIER().__str__()
        ir.defs.add(self.symbol_table.get_local(name, self.scope_stack[-1]))
        self.current_block.add(ir)

        return ir

    def visitMix(self, ctx: BSParser.MixContext):
        ir = MixIR()
        for fluid in ctx.volumeIdentifier():
            ir.uses.add(self.visitVolumeIdentifier(fluid)['variable'])

        return ir

    def visitDetect(self, ctx: BSParser.DetectContext):
        ir = DetectIR()
        ir.uses.add(self.symbol_table.get_global(ctx.IDENTIFIER(0).__str__()))
        ir.uses.add(self.symbol_table.get_local(ctx.IDENTIFIER(1).__str__(), self.scope_stack[-1]))

        return ir

    def visitHeat(self, ctx: BSParser.HeatContext):
        ir = HeatIR()
        ir.uses.add(self.symbol_table.get_local(ctx.IDENTIFIER().__str__(), self.scope_stack[-1]))
        self.current_block.add(ir)
        return ir

    def visitSplit(self, ctx: BSParser.SplitContext):
        ir = SplitIR()
        ir.uses.add(self.symbol_table.get_local(ctx.IDENTIFIER().__str__(), self.scope_stack[-1]))
        return ir

    def visitDispense(self, ctx: BSParser.DispenseContext):
        ir = DispenseIR()
        ir.uses.add(self.symbol_table.get_global(ctx.IDENTIFIER().__str__()))
        return ir

    def visitDispose(self, ctx: BSParser.DisposeContext):
        ir = DisposeIR()
        ir.uses.add(self.symbol_table.get_local(ctx.IDENTIFIER().__str__(), self.scope_stack[-1]))
        self.current_block.add(ir)
        return ir


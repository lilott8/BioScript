import random
import string

from compiler.bs_ir import *
from compiler.semantics.bs_base_visitor import BSBaseVisitor
from grammar.parsers.python.BSParser import BSParser


class BasicBlockVisitor(BSBaseVisitor):

    def __init__(self, symbol_table):
        super().__init__(symbol_table, "Basic Block Visitor")
        self.basic_blocks = list()

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

    def visitFunctionDeclaration(self, ctx: BSParser.FunctionDeclarationContext):
        name = ctx.IDENTIFIER().__str__()
        func = self.symbol_table.functions[name]
        output = ""

        self.scope_stack.append(name)
        self.symbol_table.current_scope = self.symbol_table.scope_map[name]

        output += "{}def {} (".format(self.tab, name)
        if func.args:
            for arg in func.args:
                output += "{}, ".format(arg.name)
            output = output[:-2]
        output += "):{}".format(self.nl)

        for statement in ctx.statements():
            output += self.visitStatements(statement)

        self.scope_stack.pop()
        return output

    def visitIfStatement(self, ctx: BSParser.IfStatementContext):
        ir = BranchIR()
        ir.condition = self.visitParExpression(ctx.parExpression())

        if ctx.ELSE():
            # Basic Block id it jumps to.
            ir.jumps = -1

        return ir

    def visitWhileStatement(self, ctx: BSParser.WhileStatementContext):
        ir = LoopIR()
        ir.condition = self.visitParExpression(ctx.parExpression())

        return ir

    def visitRepeat(self, ctx: BSParser.RepeatContext):
        ir = LoopIR()
        new_var = ''.join(random.choices(string.ascii_uppercase + string.digits, k=8))

        ir.condition = "{} < {}".format(new_var, ctx.INTEGER_LITERAL().__str__())

        # Add the {new_var}++ operation at the end of the loop

        return ir

    def visitMethodCall(self, ctx: BSParser.MethodCallContext):
        ir = MethodIR()

        return ir

    def visitVariableDefinition(self, ctx: BSParser.VariableDefinitionContext):
        ir = self.visitChildren(ctx)
        ir.defs.add(ctx.IDENTIFIER().__str__())

        return ir

    def visitMix(self, ctx: BSParser.MixContext):
        ir = MixIR()
        for fluid in ctx.volumeIdentifier():
            # Get variables from the table
            # variable = self.symbol_table.
            pass

        ir.uses.add()
        return ir

    def visitDetect(self, ctx: BSParser.DetectContext):
        ir = DetectIR()
        return ir

    def visitHeat(self, ctx: BSParser.HeatContext):
        ir = HeatIR()
        return ir

    def visitSplit(self, ctx: BSParser.SplitContext):
        ir = SplitIR()
        return ir

    def visitDispense(self, ctx: BSParser.DispenseContext):
        ir = DispenseIR()
        return ir

    def visitDispose(self, ctx: BSParser.DisposeContext):
        ir = DisposeIR()
        return ir

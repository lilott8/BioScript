from bioscript.visitors.targets.inkwell_visitor import InkwellVisitor
from grammar.parsers.python.BSParser import BSParser
from shared.bs_exceptions import UnsupportedOperation


class ContinuousVisitor(InkwellVisitor):

    def __init__(self, symbol_table, name="ContinuousVisitor"):
        super().__init__(symbol_table, name)

    def visitFunctionDeclaration(self, ctx: BSParser.FunctionDeclarationContext):
        raise UnsupportedOperation("Functions are not supported")

    def visitIfStatement(self, ctx: BSParser.IfStatementContext):
        raise UnsupportedOperation("IF instruction not supported")

    def visitWhileStatement(self, ctx: BSParser.WhileStatementContext):
        raise UnsupportedOperation("WHILE instruction not supported")

    def visitRepeat(self, ctx: BSParser.RepeatContext):
        raise UnsupportedOperation("REPEAT instruction not supported")

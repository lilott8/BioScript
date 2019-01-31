from bioscript.visitors.targets.inkwell_visitor import InkwellVisitor
from grammar.parsers.python.BSParser import BSParser


class ControlVisitor(InkwellVisitor):

    def __init__(self, symbol_table, name="ControlVisitor"):
        super().__init__(symbol_table, name)

    def visitMethodCall(self, ctx: BSParser.MethodCallContext):
        self.log.info(self.symbol_table.current_scope)
        return super().visitMethodCall(ctx)

from bioscript.visitors.targets.target_visitor import TargetVisitor
from grammar.parsers.python.BSParser import BSParser
from shared.bs_exceptions import UnsupportedOperation
from shared.enums.bs_properties import *


class InkwellVisitor(TargetVisitor):
    """
    In inkwell, all dispenses are implicit
    """

    def __init__(self, symbol_table, name="InkwellVisitor"):
        super().__init__(symbol_table, name)

    def visitProgram(self, ctx: BSParser.ProgramContext):
        self.scope_stack.append("main")
        self.symbol_table.current_scope = self.symbol_table.scope_map['main']

    def visitDispense(self, ctx: BSParser.DispenseContext):
        # This is implicit in this framework.
        return ""

    def visitDispose(self, ctx: BSParser.DisposeContext):
        # This is implicit in this framework
        return ""

    def visitDetect(self, ctx: BSParser.DetectContext):
        output = "detect("
        module = self.check_identifier(ctx.IDENTIFIER(0).__str__())
        material = self.check_identifier(ctx.IDENTIFIER(1).__str__())
        time = {}
        if ctx.timeIdentifier():
            time = self.visitTimeIdentifier(ctx.timeIdentifier())
            output += "{}".format(time['quantity'])
        else:
            time['quantity'] = 10.0
            time['units'] = BSTime.SECOND
            output += "10.0"
        return output

    def visitSplit(self, ctx: BSParser.SplitContext):
        raise UnsupportedOperation("Inkwell doesn't support splits.")

    def visitMethodCall(self, ctx: BSParser.MethodCallContext):
        raise UnsupportedOperation("Inkwell doesn't support splits.")

    def visitMix(self, ctx: BSParser.MixContext):
        mix = super().visitMix(ctx)
        return ""

    def visitModuleDeclaration(self, ctx: BSParser.ModuleDeclarationContext):
        return super().visitModuleDeclaration(ctx)

    def visitHeat(self, ctx: BSParser.HeatContext):
        return super().visitHeat(ctx)

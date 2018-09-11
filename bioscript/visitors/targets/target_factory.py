from bioscript.symbol_table.symbol_table import SymbolTable
from bioscript.visitors.targets.inkwell_visitor import InkwellVisitor
from bioscript.visitors.targets.mfsim_visitor import MFSimVisitor
from bioscript.visitors.targets.puddle_visitor import PuddleVisitor
from shared.enums.config_flags import Target


class TargetFactory(object):

    @staticmethod
    def get_target(target: Target, symbol_table: SymbolTable):
        if target == Target.PUDDLE:
            return PuddleVisitor(symbol_table)
        elif target == Target.INKWELL:
            return InkwellVisitor(symbol_table)
        elif target == Target.MFSIM:
            return MFSimVisitor(symbol_table)

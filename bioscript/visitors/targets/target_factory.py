from bioscript.symbol_table.symbol_table import SymbolTable
from bioscript.visitors.targets.clang_visitor import ClangVisitor
from bioscript.visitors.targets.continuous_visitor import ContinuousVisitor
from bioscript.visitors.targets.control_visitor import ControlVisitor
from bioscript.visitors.targets.mfsim_visitor import MFSimVisitor
from bioscript.visitors.targets.puddle_visitor import PuddleVisitor
from bioscript.visitors.targets.target_visitor import TargetVisitor
from shared.enums.config_flags import Target


class TargetFactory(object):

    @staticmethod
    def get_target(target: Target, symbol_table: SymbolTable) -> TargetVisitor:
        if target == Target.PUDDLE:
            return PuddleVisitor(symbol_table)
        elif target == Target.CONTINUOUS:
            return ContinuousVisitor(symbol_table)
        elif target == Target.CONTROL:
            return ControlVisitor(symbol_table)
        elif target == Target.MFSIM:
            return MFSimVisitor(symbol_table)
        else:
            return ClangVisitor(symbol_table)

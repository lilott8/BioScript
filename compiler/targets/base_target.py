import colorlog

from compiler.symbol_table import SymbolTable
from compiler.targets.inkwell_target import InkwellTarget
from compiler.targets.visitors.clang_visitor import ClangVisitor
from compiler.targets.visitors.mfsim_visitor import MFSimVisitor
from compiler.targets.visitors.puddle_visitor import PuddleVisitor
from compiler.targets.visitors.target_visitor import TargetVisitor
from shared.enums.config_flags import Target
from shared.helpers import *


class BaseTarget(object):

    def __init__(self, symbol_table: SymbolTable, name="BaseTarget"):
        self.log = colorlog.getLogger(self.__class__.__name__)
        self.config = Config.getInstance(None)
        self.symbol_table = SymbolTable
        self.name = name

    @staticmethod
    def get_target(target: Target, symbol_table: SymbolTable) -> TargetVisitor:
        if target == Target.PUDDLE:
            return PuddleVisitor(symbol_table)
        elif target == Target.INKWELL:
            return InkwellTarget(symbol_table)
        elif target == Target.MFSIM:
            return MFSimVisitor(symbol_table)
        else:
            return ClangVisitor(symbol_table)

    def map_mix(self):
        raise NotImplemented

    def map_split(self):
        raise NotImplemented

    def map_detect(self):
        raise NotImplemented

    def map_dispose(self):
        raise NotImplemented

    def map_dispense(self):
        raise NotImplemented

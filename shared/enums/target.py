from enum import IntEnum

from compiler.targets.clang_target import ClangTarget
from compiler.targets.inkwell_target import InkwellTarget
from compiler.targets.mfsim_target import MFSimTarget
from compiler.targets.puddle_target import PuddleTarget


class Target(IntEnum):
    LLVM_IR = 1
    MFSIM = 2
    PUDDLE = 4
    INKWELL = 8

    def get_target(self, program):
        if self == Target.PUDDLE:
            return PuddleTarget(program)
        elif self.value == Target.INKWELL:
            return InkwellTarget(program)
        elif self.value == Target.MFSIM:
            return MFSimTarget(program)
        else:
            return ClangTarget(program)

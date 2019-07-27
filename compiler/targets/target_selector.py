from enum import IntEnum

import compiler.data_structures.program as prog
import compiler.targets as targets


class TargetSelector(IntEnum):
    DISABLED = 0
    LLVM_IR = 1
    MFSIM = 2
    PUDDLE = 4
    INKWELL = 8

    def get_target(self, program: prog.Program):
        if self == TargetSelector.PUDDLE:
            return targets.PuddleTarget(program)
        elif self.value == TargetSelector.INKWELL:
            return targets.InkwellTarget(program)
        elif self.value == TargetSelector.MFSIM:
            return targets.MFSimTarget(program)
        else:
            return targets.ClangTarget(program)

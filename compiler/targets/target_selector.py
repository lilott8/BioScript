from enum import IntEnum

import compiler.data_structures.program as prog
import compiler.targets as targets


class TargetSelector(IntEnum):
    DISABLED = 0
    IR = 1
    LLVM_IR = 2
    MFSIM = 4
    PUDDLE = 8
    INKWELL = 16

    def get_target(self, program: prog.Program):
        if self == TargetSelector.PUDDLE:
            return targets.PuddleTarget(program)
        elif self.value == TargetSelector.INKWELL:
            return targets.InkwellTarget(program)
        elif self.value == TargetSelector.MFSIM:
            return targets.MFSimTarget(program)
        elif self.value == TargetSelector.LLVM_IR:
            return targets.ClangTarget(program)
        else:
            return targets.IRTarget(program)

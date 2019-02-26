from enum import IntEnum
from enum import IntFlag

from compiler.data_structures.bs_program import BSProgram
from compiler.targets.clang_target import ClangTarget
from compiler.targets.inkwell_target import InkwellTarget
from compiler.targets.mfsim_target import MFSimTarget
from compiler.targets.puddle_target import PuddleTarget


class Problem(IntEnum):
    BIOSCRIPT = 1
    MIX = 2
    DISPOSAL = 3
    STORAGE = 4


class ReportingLevel(IntEnum):
    NONE = 0
    WARNING = 1
    ERROR = 2


class TypeChecker(IntEnum):
    DISABLED = 0
    NAIVE = 1
    UNION = 2


class IdentifyLevel(IntFlag):
    DISABLED = 0
    PUBCHEM_ID = 1
    INCHL_KEY = 2
    CAS_NUMBER = 4
    SMILES = 8
    FORMULA = 16
    NAME = 32


class ClassifyLevel(IntFlag):
    NAIVE = 1
    SIMULATE = 2


class Target(IntFlag):
    LLVM_IR = 1
    MFSIM = 2
    PUDDLE = 4
    INKWELL = 8

    def get_target(self, program: BSProgram):
        if self == Target.PUDDLE:
            return PuddleTarget(program)
        elif self.value == Target.INKWELL:
            return InkwellTarget(program)
        elif self.value == Target.MFSIM:
            return MFSimTarget(program)
        else:
            return ClangTarget(program)

from enum import IntEnum
from enum import IntFlag


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

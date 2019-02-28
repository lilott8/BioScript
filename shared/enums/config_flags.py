from enum import IntEnum


class Problem(IntEnum):
    BIOSCRIPT = 1
    MIX = 2
    DISPOSAL = 3
    STORAGE = 4


class ReportingLevel(IntEnum):
    NONE = 0
    WARNING = 1
    ERROR = 2


class TypeCheckLevel(IntEnum):
    DISABLED = 0
    NAIVE = 1
    UNION = 2

    def typecheck(self, one: set(), two: set()):
        if self.value == TypeCheckLevel.DISABLED:
            return set()
        elif self.value == TypeCheckLevel.NAIVE or self.value == TypeCheckLevel.UNION:
            return one | two

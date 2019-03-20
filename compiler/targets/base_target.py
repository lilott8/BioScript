import abc
from enum import IntEnum

import colorlog

import compiler.data_structures.program as prog
import compiler.targets as targets


class Target(IntEnum):
    LLVM_IR = 1
    MFSIM = 2
    PUDDLE = 4
    INKWELL = 8

    def get_target(self, program: prog.Program):
        if self == Target.PUDDLE:
            return targets.PuddleTarget(program)
        elif self.value == Target.INKWELL:
            return targets.InkwellTarget(program)
        elif self.value == Target.MFSIM:
            return targets.MFSimTarget(program)
        else:
            return targets.ClangTarget(program)


class BaseTarget(metaclass=abc.ABCMeta):

    def __init__(self, program: prog.Program, name="BaseTarget"):
        self.log = colorlog.getLogger(self.__class__.__name__)
        self.program = program
        self.name = name

    @staticmethod
    def get_safe_name(name: str) -> str:
        """
        Unified manner to create program-safe names
        :param name: Name of unsafe variable.
        :return: Safe name.
        """
        return name.replace(" ", "_").replace("-", "_")

    @abc.abstractmethod
    def transform(self):
        pass

    @abc.abstractmethod
    def write_mix(self) -> str:
        pass

    @abc.abstractmethod
    def write_split(self) -> str:
        pass

    @abc.abstractmethod
    def write_detect(self) -> str:
        pass

    @abc.abstractmethod
    def write_dispose(self) -> str:
        pass

    @abc.abstractmethod
    def write_dispense(self) -> str:
        pass

    @abc.abstractmethod
    def write_expression(self) -> str:
        pass

    @abc.abstractmethod
    def write_branch(self) -> str:
        pass

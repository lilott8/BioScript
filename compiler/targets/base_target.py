from enum import IntEnum

import colorlog

import compiler.targets as targets
from compiler.data_structures.program import Program


class Target(IntEnum):
    LLVM_IR = 1
    MFSIM = 2
    PUDDLE = 4
    INKWELL = 8

    def get_target(self, configuration):
        if self == Target.PUDDLE:
            return targets.PuddleTarget(configuration)
        elif self.value == Target.INKWELL:
            return targets.InkwellTarget(configuration)
        elif self.value == Target.MFSIM:
            return targets.MFSimTarget(configuration)
        else:
            return targets.ClangTarget(configuration)


class BaseTarget(object):

    def __init__(self, configuration: 'Config', name="BaseTarget"):
        self.log = colorlog.getLogger(self.__class__.__name__)
        self.name = name
        self.config = configuration

    @staticmethod
    def get_safe_name(name: str) -> str:
        """
        Unified manner to create program-safe names
        :param name: Name of unsafe variable.
        :return: Safe name.
        """
        return name.replace(" ", "_").replace("-", "_")

    def transform(self, program: Program):
        raise NotImplemented

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

    def map_expression(self):
        raise NotImplemented

    def map_branch(self):
        raise NotImplemented

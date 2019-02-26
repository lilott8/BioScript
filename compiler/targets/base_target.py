import colorlog

import config.config
from compiler.data_structures.bs_program import BSProgram


class BaseTarget(object):

    def __init__(self, program: BSProgram, name="BaseTarget"):
        self.config = config.Config.getInstance(None)
        self.log = colorlog.getLogger(self.__class__.__name__)
        self.name = name
        self.program = program

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

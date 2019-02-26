import colorlog

from compiler.data_structures.bs_program import BSProgram
from shared.enums.config_flags import Target


class TargetManager(object):

    def __init__(self, program: BSProgram, target: Target):
        self.log = colorlog.getLogger(self.__class__.__name__)
        self.log.debug("Initializing target manager.")
        self.program = program
        self.target = target.get_target(program)

    def transform(self):
        # self.target
        self.log.info("Visiting: {}".format(self.target.name))

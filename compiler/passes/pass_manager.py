import colorlog

from compiler.data_structures.bs_program import BSProgram
from config.config import Config


class PassManager(object):

    def __init__(self, program: BSProgram):
        self.config = Config.getInstance(None)
        self.log = colorlog.getLogger(self.__class__.__name__)
        self.log.debug("Initializing pass manager.")
        self.program = program

    def transformations(self):
        pass

    def analyses(self):
        pass

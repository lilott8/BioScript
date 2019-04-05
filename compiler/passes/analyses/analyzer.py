from abc import ABCMeta, abstractmethod

import colorlog

from compiler.data_structures.program import Program


class Analyzer(metaclass=ABCMeta):

    def __init__(self, name: str):
        self.log = colorlog.getLogger(self.__class__.__name__)
        self.name = name

    @abstractmethod
    def analyze(self, program: Program):
        pass

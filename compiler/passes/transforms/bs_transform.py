from abc import ABCMeta, abstractmethod

import colorlog

from compiler.data_structures.program import Program


class BSTransform(metaclass=ABCMeta):

    def __init__(self, pass_name: str):
        self.log = colorlog.getLogger(self.__class__.__name__)
        self.name = pass_name

    @abstractmethod
    def transform(self, program: Program) -> Program:
        raise NotImplemented

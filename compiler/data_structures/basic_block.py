import copy

from compiler.bs_ir import *


class BasicBlock(object):
    id_counter = 1

    def __init__(self, name: str = ""):
        self.nid = BasicBlock.get_next_id()
        self.name = name
        # The list of BB ids this block can reach
        self.jumps = set()
        # This list of instructions in this basic block
        self.instructions = list()

    def get_leader(self) -> str:
        return self.instructions[0]

    def get_jump(self):
        return self.instructions[-1]

    def add(self, instruction: IR):
        self.instructions.append(instruction)

    def __repr__(self):
        return self.__str__()

    def __str__(self):
        output = "ID: {}\n".format(self.nid)

        for i in self.instructions:
            output += "{}\n".format(i)

        output += "=============\n"
        return output

    @staticmethod
    def get_next_id():
        tid = copy.deepcopy(BasicBlock.id_counter)
        BasicBlock.id_counter += BasicBlock.id_counter
        return tid

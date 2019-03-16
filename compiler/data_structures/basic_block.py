import colorlog

from compiler.data_structures.ir import *


class BasicBlock(object):
    id_counter = 1

    def __init__(self, name: str = ""):
        self.nid = BasicBlock.get_next_id()
        self.log = colorlog.getLogger(name=BasicBlock.__name__)
        self.name = name
        # The list of BB ids this block can reach
        self.jumps = list()
        # This list of instructions in this basic block
        self.instructions = list()
        self.defs = set()
        self.uses = set()
        self.label = None
        # Inserted phi nodes
        self.phis = set()

    def get_leader(self) -> str:
        return self.instructions[0]

    def get_jump(self):
        return self.instructions[-1]

    def add(self, instruction: IR):
        if instruction.op == IRInstruction.LABEL:
            if self.label:
                self.log.warning("Trying to add a label to an already labeled block.")
            self.label = instruction
        elif instruction.op == IRInstruction.JUMP:
            self.jumps.append(instruction)
        elif instruction.op == IRInstruction.CONDITIONAL:
            self.instructions.append(instruction)
        else:
            self.instructions.append(instruction)

    def add_defs(self, var: Variable):
        self.defs.add(var.name)

    def add_uses(self, var: Variable):
        self.uses.add(var.name)

    def __repr__(self):
        return self.__str__()

    def __str__(self):
        output = "\nID: {}\n".format(self.nid)
        output += "{}\n".format(self.label)

        output += "defs: {"
        defs = ""
        for key in self.defs:
            defs += "{}, ".format(key)
        if defs:
            defs = defs[:-2]
        output += "{}}}\n".format(defs)

        output += "uses: {"
        uses = ""
        for key in self.uses:
            uses += "{}, ".format(key)
        if uses:
            uses = uses[:-2]
        output += "{}}}\n".format(uses)

        output += "Instructions: \n"
        for i in self.instructions:
            output += "\t{}\n".format(i)

        output += "=============\n"
        return output

    @staticmethod
    def get_next_id():
        tid = BasicBlock.id_counter
        BasicBlock.id_counter = BasicBlock.id_counter + 1
        return tid

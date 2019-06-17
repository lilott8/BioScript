import colorlog

# import compiler.data_structures.ir as ir
from compiler.data_structures.ir import *


# import compiler.data_structures.variable as variable


class BasicBlock(object):
    id_counter = 1

    def __init__(self, name: str = ""):
        self.nid = BasicBlock.get_next_id()
        self.log = colorlog.getLogger(name=BasicBlock.__name__)
        self.name = name
        # The list of BB ids this block can reach.
        self.jumps = list()
        # This list of instructions in this basic block.
        self.instructions = list()
        # The def(s)/use(s) of a block.
        # These only hold the variable name,
        # not the entire variable object.
        self.defs = set()
        self.uses = set()
        self.label = None
        # Inserted phi nodes.
        self.phis = set()
        # The dag that represents this basic block.
        self.dag = None

    def get_leader(self) -> str:
        return self.instructions[0]

    def get_jump(self):
        jumps = list()
        for jump in self.jumps:
            if jump.op == IRInstruction.JUMP:
                jumps.append(jump)
        return jumps

    def get_returns(self):
        for jump in self.jumps:
            if jump.op == IRInstruction.RETURN:
                return jump
        return None

    def get_call(self):
        for jump in self.jumps:
            if jump.op == IRInstruction.CALL:
                return jump
        return None

    def add(self, instruction: IR):
        # All statements have def/uses.
        if hasattr(instruction, 'defs'):
            if instruction.defs is not None:
                self.defs.add(instruction.defs.name)
        if hasattr(instruction, 'uses'):
            for use in instruction.uses:
                if isinstance(use, Variable):
                    self.uses.add(use.name)

        if instruction.op == IRInstruction.LABEL:
            if self.label:
                self.log.warning("Trying to add a label to an already labeled block.")
            self.label = instruction
        elif instruction.op == IRInstruction.JUMP:
            self.jumps.append(instruction.jumps)
            self.instructions.append(instruction)
        elif instruction.op == IRInstruction.CONDITIONAL:
            self.jumps.append(instruction.true_branch)
            self.jumps.append(instruction.false_branch)
            self.instructions.append(instruction)
        elif instruction.op == IRInstruction.CALL:
            self.jumps.append(instruction.function.name)
            self.instructions.append(instruction)
        elif instruction.op == IRInstruction.RETURN:
            self.jumps.append(instruction.return_to)
            self.jumps.append(instruction.name)
            self.instructions.append(instruction)
        else:
            self.instructions.append(instruction)

    # def add_defs(self, var: variable.Variable):
    #     self.defs.add(var.name)
    #
    # def add_uses(self, var: variable.Variable):
    #     self.uses.add(var.name)

    def __repr__(self):
        return self.__str__()

    def __str__(self):
        dag = "True" if self.dag is not None else "False"
        output = "\nID: {}\nHas DAG: {}\n".format(self.nid, dag)
        output += "{}\n".format(self.label)
        jumps = "Jumps: "
        in_jumps = False
        for j in self.jumps:
            jumps += "{} -- \t".format(j)
            in_jumps = True
        if in_jumps:
            jumps = jumps[:-5]
        output += jumps + "\n"

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

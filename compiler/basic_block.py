class BasicBlock(object):

    def __init__(self, nid: int = -1, name: str = ""):
        self.nid = nid
        self.name = name
        # The list of BB ids this block can reach
        self.jumps = set()
        # This list of instructions in this basic block
        self.instructions = list()

    def get_leader(self) -> str:
        return self.instructions[0]

    def get_jump(self):
        return self.instructions[-1]

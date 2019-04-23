from compiler.data_structures import Program
from compiler.passes.analyses.bs_analysis import BSAnalysis


class Chain(object):

    def __init__(self, block: int, instruction: int, subsumed: str):
        self.block = -1
        self.instruction = -1
        self.subsumed_by = -1


class DefUseChains(BSAnalysis):

    def __init__(self):
        super().__init__("Def/Use Chains")
        # This maps any dispense to any necessary disposals
        self.dispose_dispense_chain = dict()
        # this maps any variables to any
        self.def_use_chain = dict()
        # https://github.com/lilott8/ChemCompiler-Deprecated-/blob/master/src/main/java/compilation/datastructures/basicblock/DependencySlicedBasicBlock.java
        # https://en.wikipedia.org/wiki/Use-define_chain

    def analyze(self, program: Program) -> dict:
        # for root in program.functions:
        #     for nid, block in program.functions[root]['blocks'].items():
        #         for instruction in block.instructions:
        # self.log.info(instruction)
        return {'name': self.name, 'result': None}

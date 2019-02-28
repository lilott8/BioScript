from compiler.data_structures.bs_program import BSProgram
from compiler.passes.analyses.bs_analysis import BSAnalysis


class CallGraph(BSAnalysis):

    def __init__(self):
        super().__init__("CallGraph")

    def analyze(self, program: BSProgram):
        pass

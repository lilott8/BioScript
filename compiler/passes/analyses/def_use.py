from compiler.data_structures import Program
from compiler.passes.analyses.bs_analysis import BSAnalysis


class DefUseChains(BSAnalysis):

    def __init__(self):
        super().__init__("Def/Use Chains")

    def analyze(self, program: Program) -> dict:
        for root in program.functions:
            self.log.info(root)
        return {'name': self.name, 'result': None}

from problem.problem import Problem
from bioscript.bs_translator import BSTranslator


class BioScript(Problem):

    def __init__(self):
        Problem.__init__(self)
        self.translator = BSTranslator()

    def run(self):
        self.translator.translate()

from bioscript.bs_translator import BSTranslator
from problem.problem import Problem


class BioScript(Problem):

    def __init__(self):
        Problem.__init__(self)
        self.translator = BSTranslator()

    def run(self):
        self.translator.translate()

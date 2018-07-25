from problem.problem import Problem
from typechecker.bs_translator import BSTranslator


class TypeCheck(Problem):

    def __init__(self):
        Problem.__init__(self)
        self.translator = BSTranslator()

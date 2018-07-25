from .problem import Problem
from typechecker.bs_translator import BSTranslator


class Mix(Problem):

    def __init__(self):
        Problem.__init__(self)
        self.log.info("Mix problem.")
        self.translator = BSTranslator()

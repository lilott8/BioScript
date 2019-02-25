from compiler.compiler import BSCompiler
from problem.problem import Problem


class BioScript(Problem):

    def __init__(self):
        Problem.__init__(self)
        self.compiler = BSCompiler()

    def run(self):
        self.compiler.compile()

from typechecker.solvers.base_solver import BaseSolver
import z3


#z3-solver can be installed through: pip install z3-solver
class Z3Solver(BaseSolver):

    def __init__(self):
        BaseSolver.__init__(self)
        self.solver = z3.Solver()

    def solve(self, problem):
        self.solver.solve(problem)

    def check(self):
        return self.solver.check()

    def model(self):
        return self.solver.model()

    def create_int(self, var_name):
        return z3.Int(var_name)

    def create_real(self, var_name):
        return z3.Real(var_name)






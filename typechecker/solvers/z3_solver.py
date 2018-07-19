from typechecker.solvers.base_solver import BaseSolver


class Z3Solver(BaseSolver):

    def __init__(self):
        BaseSolver.__init__(self)

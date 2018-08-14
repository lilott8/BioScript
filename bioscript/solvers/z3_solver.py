# z3prover.github.io/api/html/namespacez3py.html#a09fe122cbfbc6d3fa30a79850b2a2414
# z3-solver can be installed through: pip3 install z3-solver
import z3

from bioscript.solvers.base_solver import BaseSolver


class Z3Solver(BaseSolver):

    def __init__(self):
        BaseSolver.__init__(self)

    def solve(self, problem):
        if self.config.debug:
            self.log.info("z3 version: {}".format(z3.get_full_version()))
        try:
            solver = z3.Solver()
            bool_expr = z3.parse_smt2_string(problem)
            solver.add(bool_expr)
            status = solver.check()
            if status == z3.CheckSatResult(z3.Z3_L_TRUE):
                self.log.trace('This BioScript program is safe.')
                return True
            else:
                self.log.error('This BioScript program may be unsafe for execution, halting compilation')
                return False

        except z3.Z3Exception as e:
            self.log.error('There was an error solving the given constraints')
            self.log.error(str(e))
            return False

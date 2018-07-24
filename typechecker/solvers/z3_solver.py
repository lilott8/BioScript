from typechecker.solvers.base_solver import BaseSolver
import z3

#z3prover.github.io/api/html/namespacez3py.html#a09fe122cbfbc6d3fa30a79850b2a2414

#parse_smt2_file, parse_smt2_string
#z3-solver can be installed through: pip3 install z3-solver
class Z3Solver(BaseSolver):

    def __init__(self):
        BaseSolver.__init__(self)
    
    def solve_with_smt2(self, smt2_string):
        try:
            solver    = z3.Solver()
            solver.add(z3.parse_smt2_string(smt2_string))
            status    = solver.check()
            if status == z3.CheckSatResult(z3.Z3_L_TRUE):
                log.trace('This BioScript program is safe.')
                return True
            else:
                log.error('This BioScript program may be unsafe for execution, halting compilation')
                return False

        except z3.Z3Exception as e:
            log.error('There was an error solving the given constraints')
            log.error(str(e))
            return False












# z3prover.github.io/api/html/namespacez3py.html#a09fe122cbfbc6d3fa30a79850b2a2414
# z3-solver can be installed through: pip3 install z3-solver
import z3

#from solvers import BaseSolver


class Z3Solver:#(BaseSolver):

    def __init__(self):
        pass
        #BaseSolver.__init__(self)

    def solve(self, problem) -> bool:
        # if self.config.debug:
        # self.log.info("z3 version: {}".format(z3.get_full_version()))
        try:
            solver = z3.Solver()
            bool_expr = z3.parse_smt2_string(problem)
            solver.add(bool_expr)
            status = solver.check()
            if status == z3.sat:
                self.log.trace('This BioScript program is safe.')
                return True
            else:
                self.log.error('This BioScript program may be unsafe for execution, halting compilation')
                return False

        except z3.Z3Exception as e:
            self.log.error('There was an error solving the given constraints')
            self.log.error(str(e))
            return False




    def solve_graph(self, ver_weights, uses, edges):
        """
        Parameters:
        ver_weights: length of weights == number of vertices in graph, the elements correspond to the weights of the nodes.
        uses:        list of amount of colors that can be used.
        edges:       list of tuples such that (0, 1) = edge between nodes 0 and 1 
    
        Output:
        list of colors the nodes can be colored.
        """
        solver          = z3.Optimize()
        v_list          = [z3.Int('x_%s' % x) for x in range(len(ver_weights))]
        v_constraint    = [z3.And(x >= 0, x < len(ver_weights)) for x in v_list]
        edges           = [v_list[v1] != v_list[v2] for v1, v2 in edges]
        bin_constraint  = [z3.PbLe(tuple((ver == v_id, weight) for ver, weight in zip(v_list, ver_weights)), use) \
                           for v_id, use in enumerate(uses)]
    
        solver.add(v_constraint + edges + bin_constraint)
        solver.minimize(z3.Sum(v_list))
        return solver.model() if solver.check() == z3.sat else None


'''
s = Z3Solver()
model = s.solve_graph([5, 3, 2, 4], [2, 5, 4, 3], [(0, 1), (1, 3), (2, 3), (0, 2)])
if model != None:
    print(model)
else:
    print('unsat')
'''




# z3prover.github.io/api/html/namespacez3py.html#a09fe122cbfbc6d3fa30a79850b2a2414
# z3-solver can be installed through: pip3 install z3-solver
import z3
import json
from functools import reduce


class Z3Solver:#(BaseSolver):

    def __init__(self):
        pass

    def solve(self, problem) -> bool:
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

    
    @staticmethod
    def not_safe(grpA, grpB, safe = lambda x, y: False):
        for g1 in grpA:
            for g2 in grpB:
                if not safe(g1, g2):
                    return True
        return False


    @staticmethod
    def _graph_coloring_constraints(manifest, storage, color, safe_funct = lambda x, y: False):
        
        #all colors must be within 0 and k colors
        k = len(storage)
        limits = [z3.And(0 <= c, c < k) for c in color ]
        
        #edges for graph coloring
        edges  = []

        #edges between different chemicals
        for i, m1 in enumerate(manifest):
            for j, m2 in enumerate(manifest):
                if i != j and Z3Solver.not_safe(m1['reactive_groups'], m2['reactive_groups'], safe=safe_funct):
                    edges.append( color[i] != color[j] )

        #edges between chemicals & cabinets
        for i, m in enumerate(manifest):
            for j, s in enumerate(storage):
                for c in s['chemicals']:
                    if Z3Solver.not_safe(m['reactive_groups'], c['reactive_groups'], safe=safe_funct):
                        edges.append( color[i] != j )
                        break

        return limits + edges   #, z3.Sum(color)


    @staticmethod
    def _bin_packing_constraints(manifest, storage, color, volume):
        constraint = []
        #heuristic = []
        limits = [z3.And(0 <= v, v <= s['volume_left']) for v,s in zip(volume,storage) ]
        
        for i, stor in enumerate(storage):
            summation  = z3.Sum([z3.If(col==i, vol, 0) for col, vol in zip(color, volume)])
            constraint.append( summation <= stor['volume_left'] )
            #heuristic.append(  z3.Sum([z3.If(z3.Or(summation==0, summation==stor['volume_left']), 1, 0)]) )
        return limits + constraint     #, z3.Sum(heuristic)


    @staticmethod
    def _coalesing_constraints(manifest, storage, color, volume):
        constraint = []
        #heuristic  = z3.Int('coalesing_heuristic')

        chemical_dict = {}
        for s in storage:
            for c in s['chemicals']:
                name = c['chemical']
                if not name in chemical_dict:
                    chemical_dict[name] = 0
                chemical_dict[name] += c['total_volume'] - c['current_volume']

        for key, value in chemical_dict.items():
            #value=0 means no coalesing, therefore no need to have a constraint.
            if value != 0:
                summation = z3.Sum([m['volume']-v for m,v in zip(manifest,volume) if m['chemical'] == key])
                constraint.append(summation <= value)
                #heuristic = heuristic + summation
        
        return constraint    #, heuristic


    @staticmethod
    def solve_constraints(file_name, safe_funct = lambda x, y: False, sol=True):
        """
        open .json file and solve the problem given in the file.
        safe_funct determines whether chemicals x, y can be safely mixed
        solution variable determines whether return the solution or not, or just report True/False
        """
        json_data = {}
        with open(file_name) as file:
            json_data = json.loads(file.read())
        if not json_data:
            return None

        manifest  = json_data['manifest']
        storage   = json_data['storage']

        #???? z3.Optimize performs better than z3.Solver?????
        solver = z3.Optimize()
        color  = [z3.Int('color_of_%s_%s' % (m['chemical'],i))  for i,m in enumerate(manifest)]
        volume = [z3.Int('volume_of_%s_%s' % (m['chemical'],i)) for i,m in enumerate(manifest)]

        coloring_constraints    = Z3Solver._graph_coloring_constraints(manifest, storage, color, safe_funct=safe_funct) 
        bin_packing_constraints = Z3Solver._bin_packing_constraints(manifest, storage, color, volume)
        coalesing_constraints   = Z3Solver._coalesing_constraints(manifest, storage, color, volume)

        solver.add(coloring_constraints + bin_packing_constraints + coalesing_constraints)
        
        #I measured, heuristics do not help the problem at all, they actually hurt the performance
        #opt.minimize(coloring_heuristic)
        #opt.maximize(bin_packing_heuristic)
        #opt.maximize(coalesing_heuristic)
        if not sol:
            return solver.check() == z3.sat

        if solver.check() == z3.sat:
            model = solver.model()
            return [(model.evaluate(col), model.evaluate(vol)) for col, vol in zip(color, volume)]
        else:
            return None










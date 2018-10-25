# z3prover.github.io/api/html/namespacez3py.html#a09fe122cbfbc6d3fa30a79850b2a2414
# z3-solver can be installed through: pip3 install z3-solver
import z3
import json
from functools import reduce

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

    
    @staticmethod
    def not_safe(grpA, grpB, safe = lambda x, y: False):
        for g1 in grpA:
            for g2 in grpB:
                if not safe(g1, g2):
                    print('compare: ', g1, g2)
                    return True
        return False

   
    @staticmethod
    def solve_file(file_name, safe_function = lambda x, y: False, sol=True):
        parsed = {}
        with open(file_name) as file:
            parsed = json.loads(file.read())
        if parsed['problem'] == 'storage':
            stored_chem_volumes = []
            stored_reactive_groups = []
            chem_volumes = []
            reactive_groups = []
            for n, shelf in enumerate(parsed['storage']):
                stored_reactive_groups.append([])
                stored_chem_volumes.append([])
                for chem in shelf:
                    stored_reactive_groups[n] += chem['reactive_groups']
                    x = chem['total_volume'] - chem['current_volume']
                    if x > 0:
                        stored_chem_volumes[n].append(x)
            for chem in parsed['manifest']:
                chem_volumes.append(chem['volume'])
                reactive_groups.append(chem['reactive_groups'])

            edges_chems = []
            for i, grpA in enumerate(reactive_groups):
                for j, grpB in enumerate(reactive_groups):
                    if i != j and Z3Solver.not_safe(grpA, grpB, safe=safe_function):
                        edges_chems.append((i, j))
            edges_shelves = []
            for i, grpA in enumerate(reactive_groups):
                for j, grpB in enumerate(stored_reactive_groups):
                    if Z3Solver.not_safe(grpA, grpB, safe=safe_function):
                        edges_shelves.append((i, j))
            return Z3Solver.solve_recursive_bin_packing(stored_chem_volumes, chem_volumes, edges_chems, edges_shelves=edges_shelves, sol=sol)
        elif parsed['problem'] == 'drain':
            pass

    @staticmethod
    def solve_recursive_bin_packing(shelves, chem_volumes, edges_chems, edges_shelves=None, sol=True):
        solver = z3.Optimize()
        chems  = [z3.Int('c%s' % x) for x in range(len(chem_volumes))]
        chems_constraint = [z3.And(c >= 0, c < len(chem_volumes)) for c in chems]
        edges  = [chems[v0] != chems[v1] for v0, v1 in edges_chems]
        shelf_vol  = [z3.Int('vol%s_%s' % (x, y)) for x, shelf in enumerate(shelves) for y in range(len(shelf))]
        shelf_vol_constraint = [z3.And(vol >= 0, vol <= vol_full) for vol, vol_full in zip(shelf_vol, reduce(lambda x, y: x + y, shelves))]

        bin_color_array = [[z3.Int('bin_color%s_%s' % (x, y)) for y in range(len(shelves[x]))] for x, shelf in enumerate(shelves)]
        bin_chems  = [z3.Int('bin_chem%s_%s' % (x, y)) for x, s in enumerate(shelves) for y in range(len(s))]
        for bins in bin_color_array:
            eq = [n1==bins[0] for n1 in bins]
            solver.add(eq)

        for x, y in edges_shelves:
            solver.add([chems[x] != color for color in bin_color_array[y]])

        bin_colors = reduce(lambda x, y: x+y, bin_color_array)
        bin_constraint = [z3.Sum([z3.If(z3.And(bin_color==chems[i], bin_chem==i), vol, 0) for bin_color, bin_chem, vol in zip(bin_colors, bin_chems, shelf_vol)]) == chem_vol for i, chem_vol in enumerate(chem_volumes)]
        
        solver.add(chems_constraint + edges + shelf_vol_constraint + bin_constraint)
        sum_max = ([z3.If(z3.Or(s==0, s==vol_full), 1, 0) for s, vol_full in zip(shelf_vol, reduce(lambda x, y: x + y, shelves))])
        if sum_max:
            solver.maximize(z3.Sum(sum_max))
        solver.minimize(z3.Sum(chems))
        if sol==False:
            return solver.check() == z3.sat

        if solver.check() == z3.sat:
            model = solver.model()
            return [('%s=%s' % (col, model.evaluate(col)), \
                     '%s=%s' % (chem, model.evaluate(chem)), \
                     '%s=%s' % (vol, model.evaluate(vol))) \
                     for chem, vol, col in zip(bin_chems, shelf_vol, bin_colors)]
        return None


    @staticmethod
    def solve_graph(ver_weights, uses, edges):
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


    @staticmethod
    def solve_problem(file_name, safe_funct = lambda x, y: False, sol=True):
        """
        open .json file and solve the problem given in the file.
        safe_funct determines whether chemicals x, y can be safely mixed
        solution variable determines whether return the solution or not, or just report True/False
        """
        parsed = {}
        with open(file_name) as file:
            parsed = json.loads(file.read())

        quantity = parsed['storage']['quantity']
        solver   = z3.Optimize()

        #chemicals to be stored
        chems_store_ids = [chem['chemical']['pubchem_id'] for chem in parsed['manifest'] if chem != {} ]
        chems_store_num = len(chems_store_ids)
        chems_store_groups = [chem['chemical']['reactive_groups'] for chem in parsed['manifest'] if chem != {}]

        #chemicals already stored as (shelf num, id, volume)
        chems_binned_shelf_num = [num for shelves in parsed['storage']['shelves'] for num, chem in enumerate(shelves['store']) if chem != {}]
        chems_binned_ids = [chem['chemical']['pubchem_id'] for shelves in parsed['storage']['shelves'] for chem in shelves['store'] if chem != {}]
        chems_binned_groups = [chem['chemical']['reactive_groups'] for shelves in parsed['storage']['shelves'] for chem in shelves['store'] if chem != {}]

        #which chemicals can be safely stored together.    
        chems_to_store_shelf_num   = [z3.Int('chem_store_%s' %x) for x in range(chems_store_num)]
        chems_to_store_shelf_num_c = [z3.And(x >= 0, x < quantity) for x in chems_to_store_shelf_num]
        
        #edges between chemicals that need to be stored:
        for i, chem_group1 in enumerate(chems_store_groups):
            for j, chem_group2 in enumerate(chems_store_groups):
                if i != j:
                    for chem1 in chem_group1:
                        for chem2 in chem_group2:
                            if not safe_funct(chem1, chem2):
                                solver.add(chems_to_store_shelf_num[i] != chems_to_store_shelf_num[j])
        '''pubchem_id's
        for i in range(chems_store_num):
            for j in range(i, chems_store_num):
                if i != j and not safe_funct(chems_store_ids[i], chems_store_ids[j]):
                    solver.add(chems_to_store_shelf_num[i] != chems_to_store_shelf_num[j])
        '''
        #edges between chemicals that need to be stored and chemicals already stored:
        for i, chem_group1 in enumerate(chems_store_groups):
            for j, chem_group2 in enumerate(chems_binned_groups):
                for chem1 in chem_group1:
                    for chem2 in chem_group2:
                        if not safe_funct(chem1, chem2):
                            solver.add(chems_to_store_shelf_num[i] != chems_binned_shelf_num[j])

        '''pubchem_id's
        for i in range(chems_store_num):
            for j in range(chems_binned_num):
                if not safe_funct(chems_store_ids[i], chems_binned_ids[j]):
                    solver.add(chems_to_store_shelf_num[i] != chems_binned_shelf_num[j])
        '''
        #bin constraint if we have a storage problem:
        if parsed['problem'] == 'storage':
            bin_volumes = [(shelves['volume']['max'] - shelves['volume']['current']) for shelves in parsed['storage']['shelves']]
            chems_store_volume = [chem['chemical']['volume'] for chem in parsed['manifest'] if chem != {} ]
            bin_constraint = [z3.PbLe(tuple((shelf == bin_num, vol) for shelf, vol in zip(chems_to_store_shelf_num, chems_store_volume)), volume) \
                      for bin_num, volume in enumerate(bin_volumes)]
            solver.add(bin_constraint)

        solver.add(chems_to_store_shelf_num_c)
        solver.minimize(z3.Sum(chems_to_store_shelf_num))
        
        if not sol:
            return solver.check() == z3.sat
 
        #check & solve: 
        if solver.check() == z3.sat:
            model = solver.model()
            return [(num, model.evaluate(num)) for num in chems_to_store_shelf_num]
        else:
            return None

'''
#print('problem 1: ')
ret = Z3Solver.solve_recursive_bin_packing([[400, 400, 400, 4000], [200, 200]],
                                            [200, 400, 200, 4000, 400, 400], 
                                            [(0, 1), (1, 2), (2, 3)])
if ret != None:
    for r in ret:
        print(r)
else:
    print('unsat')

#print('problem 2: ')
#ret2 = Z3Solver.solve_recursive_bin_packing([[100, 100], [100], [50]], 
#                                            [100, 200, 50], 
#                                            [(0, 1)])
#if ret2 != None:
#    print('sat')#for r in ret2:
    #    print(r)
#else:
#    print('unsat')
'''


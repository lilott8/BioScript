# z3prover.github.io/api/html/namespacez3py.html#a09fe122cbfbc6d3fa30a79850b2a2414
# z3-solver can be installed through: pip3 install z3-solver
import z3
import json

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

        #chemicals to store as (id, volume)
        chems_store_ids = [chem['chemical']['pubchem_id'] for chem in parsed['manifest'] if chem != {} ]
        chems_store_volume = [chem['chemical']['volume'] for chem in parsed['manifest'] if chem != {} ]
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






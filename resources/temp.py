import json
import z3

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


def solve_problem(file_name):
    '''
    open .json file and solve the problem given in the file.
    '''
    parsed = {}
    with open(file_name) as file:
        parsed = json.loads(file.read())

    quantity = parsed['storage']['quantity']
    #^^^^^^^
    #number of shelves in storage,
    #this variable will be used to
    #determine number of vertices in graph
    #

    #Perhaps this is slow, but doing it this way for readability...
    solver   = z3.Optimize()
    
    #store chemicals as (id, volume taken up)
    chems_to_store       = [(chem['chemical']['pubchem_id'], chem['chemical']['volume']) \
                            for chem in parsed['manifest'] if chem != {} ]
    chems_binned         = [(chem['chemical']['pubchem_id'], chem['chemical']['volume']) \
                            for shelves in parsed['storage']['shelves'] \
                                for chem in shelves['store'] if chem != {} ]
    chems_all            = chems_to_store + chems_binned

    bin_volumes = [(shelves['volume']['max'] - shelves['volume']['current']) for shelves in parsed['storage']['shelves']]
    
    chems_to_store_color = [z3.Int('mani_%s' % x) for x in range(len(chems_to_store))]
    chems_binned_color   = [z3.Int('bin_%s' %x) for x in range(len(chems_binned))]
    vertex_constraint    = [z3.And(v >= 0, v < quantity) for v in chems_all]
    #edges, bin constraint
    edges                = ...
    bin_constraint       = ...


solve_problem('storage.json')




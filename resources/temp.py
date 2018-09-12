import json

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

    parsed = {}
    with open(file_name) as file:
        parsed = json.loads(file.read())

    quantity = parsed['storage']['quantity']
    print(quantity)
    for shelves in parsed['storage']['shelves']:
    
        #create graph for modeling shelf storage:
        for chem in shelves['store']:
            print('    ', chem)#['pubchem_id']

            #figure bin storage:
            print('     quantity: ', shelves['quantity'])#['max'], ['current'], ['reactive_groups']
            print('     volume:   ', shelves['volume'])  #['max'], ['current'], ['reactive_groups']


    print('MANIFEST: ')
    for chem in parsed['manifest']:
        #create graph for chemicals to be stored:
        print('    ', chem)#['volume']['pubchem_id']['reactive_groups']




solve_problem('storage.json')




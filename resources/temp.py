import json
import z3

def solve_problem(file_name, safe_funct = lambda x, y: False):
    """
    open .json file and solve the problem given in the file.
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

    #chemicals already stored as (shelf num, id, volume)
    chems_binned_shelf_num = [num for shelves in parsed['storage']['shelves'] for num, chem in enumerate(shelves['store']) if chem != {}]
    chems_binned_ids = [chem['chemical']['pubchem_id'] for shelves in parsed['storage']['shelves'] for chem in shelves['store'] if chem != {}]
    chems_binned_num = len(chems_binned_ids)
    bin_volumes = [(shelves['volume']['max'] - shelves['volume']['current']) for shelves in parsed['storage']['shelves']]

    #which chemicals can be safely stored together.    
    chems_to_store_shelf_num   = [z3.Int('chem_store_%s' %x) for x in range(chems_store_num)]
    chems_to_store_shelf_num_c = [z3.And(x >= 0, x < quantity) for x in chems_to_store_shelf_num]
    
    #edges:
    for i in range(chems_store_num):
        for j in range(i, chems_store_num):
            if not safe_funct(chems_store_ids[i], chems_store_ids[j]):
                solver.add(chems_to_store_shelf_num[i] != chems_to_store_shelf_num[j])

    for i in range(chems_store_num):
        for j in range(chems_binned_num):
            if not safe_funct(chems_store_ids[i], chems_binned_ids[j]):
                solver.add(chems_to_store_shelf_num[i] != chems_binned_shelf_num[j])

    #bin constraint:
    bin_constraint = [z3.PbLe(tuple((shelf == bin_num, vol) for shelf, vol in zip(chems_to_store_shelf_num, chems_store_volume)), volume) \
                      for bin_num, volume in enumerate(bin_volumes)]
    solver.add(bin_constraint)
    solver.minimize(z3.Sum(chems_to_store_shelf_num))
    
    #check & solve: 
    if solver.check() == z3.sat:
        model = solver.model()
        return [(num, model.evaluate(num)) for num in chems_to_store_shelf_num]
    else:
        return None


m = solve_problem('storage.json', lambda x, y: x not in {1, 7, 15} and y not in {1, 7, 15})
if m != None:
    print(m)
else:
    print('unsat')



import networkx as nx

from compiler.data_structures import Program
from compiler.passes.analyses.bs_analysis import BSAnalysis


class VolumeTracker(BSAnalysis):
    def __init__(self):
        super().__init__("Volume Tracking") # Sets the name to Volume Tracking?

    def analyze(self, program: Program) -> dict: # The main function of the class
        print("Now tracking volume...")          # Debugging statement

        variable_volume = dict();                # The dict that will store the volumes of relevent variables

        for root in program.functions:
            for nid, block in program.functions[root]['blocks'].items():
                print(nid)
                print(block.instructions)
                print("Defs: " + str(block.defs))
                print("Uses: " + str(block.uses))

        print("Symbol Table:")
        print("globals: ")
        print(program.symbol_table.globals)

        print("functions: ")
        print(program.symbol_table.functions)

        print("scopes: ")
        print(program.symbol_table.scope_map)

        print("locals: ")
        for scope in program.symbol_table.scope_map:
            print(program.symbol_table.scope_map[scope])

            for var in program.symbol_table.scope_map[scope].locals:
                print(type(program.symbol_table.scope_map[scope].locals[var]))
                print(program.symbol_table.scope_map[scope].locals[var])

        return {'name': self.name, 'result': None} # Not sure what is going on here, but its needed to prevent a crash
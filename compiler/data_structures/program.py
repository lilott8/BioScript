from compiler.data_structures.symbol_table import SymbolTable


class Program(object):
    """
    This class models the input program and
    stores various data about the program.
    """

    def __init__(self, functions: dict = dict, entry_point: int = 1, config: 'Config' = None,
                 symbol_table: SymbolTable = None, bb_graph=None, name: str = "program",
                 ssa_form: bool = False, globalz: dict = dict, calls: dict = dict):
        # A dict: id->basic block
        self.functions = functions
        # The main entry point for the program
        self.entry_point = entry_point
        # The symbol table for the program
        self.symbol_table = symbol_table
        # The basic block based control flow graph
        self.bb_graph = bb_graph
        # The name of the graph
        self.name = name
        # Is this program in SSA form?
        self.ssa_form = ssa_form
        # Storing different analysis here (liveness, call graph, etc)
        self.analysis = dict()
        # Keep track of the globals
        self.globalz = globalz
        # keep the call graph.
        self.calls = calls
        # The config object
        self.config = config
        # The data that needs writing.
        self.write = dict()
        # for source, destinations in calls.items():
        #     for destination in destinations:
        #         self.bb_graph.add_edge(self.functions[source]['entry'], self.functions[destination]['entry'])

import networkx as nx

from compiler.data_structures import Program
from compiler.passes.analyses.bs_analysis import BSAnalysis


class VolumeTracker(BSAnalysis):
    def __init__(self):
        super().__init__("Volume Tracking") # Sets the name to Volume Tracking?

    def analyze(self, program: Program) -> dict: # The main function of the class
        print("Now tracking volume...")          # Debugging statement

        for n, d in program.bb_graph.nodes(data=True): # Try and iterate through the basic blocks in program
            print(n)
            print(str("Type of d: " + str(type(d))))
            print(d)
        return {'name': self.name, 'result': None} # Not sure what is going on here, but its needed to prevent a crash
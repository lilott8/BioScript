import networkx as nx

from compiler.data_structures import Program
from compiler.passes.analyses.bs_analysis import BSAnalysis
from compiler.data_structures.ir import *


class VolumeTracker(BSAnalysis):
    def __init__(self):
        super().__init__("Volume Tracking") # Sets the name to Volume Tracking?

    def analyze(self, program: Program) -> dict: # The main function of the class
        print("Now tracking volume...")          # Debugging statement

        variable_volume = dict();                # The dict that will store the volumes of relevent variables

        for root in program.functions:

            print("Functions from graph: ")
            for node, data in program.bb_graph.nodes(data=True):
                print(program.functions[root]['blocks'][node])

                for i in program.functions[root]['blocks'][node].instructions:
                    print(type(i))
                    #print(i)
                    print(i.defs)
                    handle(self, i)


        return {'name': self.name, 'result': None} # Not sure what is going on here, but its needed to prevent a crash


def handle(self, instruction : IR): # The meat of the logic. Just ferries out the functions based on the type of instruction.
    if (type(instruction) == Dispense):
        handle_dispense(self, instruction.defs)
        return

    if (type(instruction) == Dispose):
        handle_dispose(self, instruction.defs)
        return

    if (type(instruction) == Mix):
        handle_mix(self, instruction.defs)
        return

    if (type(instruction) == Split):
        handle_split(self, instruction.defs)
        return





def handle_dispense(self, instructions : dict):
    print("Handling dispense...")

def handle_dispose(self, instructions : dict):
    print("Handling dispose...")

def handle_mix(self, instructions : dict):
    print("Handling mix...")

def handle_split(self, instructions : dict):
    print("Handling split...")

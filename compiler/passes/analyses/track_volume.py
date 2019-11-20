import networkx as nx

from compiler.data_structures import Program
from compiler.passes.analyses.bs_analysis import BSAnalysis
from compiler.data_structures.ir import *


class VolumeTracker(BSAnalysis):

    variable_volume = dict();                # The dict that will store the volumes of relevent variables

    violation_found = False

    def __init__(self):
        super().__init__("Volume Tracking") # Sets the name to Volume Tracking?

    def analyze(self, program: Program) -> dict: # The main function of the class
        print("Now tracking volume...")          # Debugging statement

        

        for root in program.functions:

            print("Functions from graph: ")
            for node, data in program.bb_graph.nodes(data=True):
                print(program.functions[root]['blocks'][node])

                for i in program.functions[root]['blocks'][node].instructions:
                    print(type(i))
                    #print(i)
                    print(i.defs)
                    handle(self, i)
                    print(self.variable_volume)

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

    quantity = 10; # This is the default value. I don't have a way of tracking custom volumes, so we will assume everything is default for now.

    # Initialize the structures we will use later on
    entry = dict() # The dict that will hold our new entry in the variable_volume ds
    volumes = list() # The list that will holds the volumes stored at each index


    volumes.append(quantity)

    # Build the entry dict
    entry['size'] = instructions['size']
    entry['volumes'] = volumes

    self.variable_volume[instructions['name']] = entry

    print("Handling dispense...")

def handle_dispose(self, instructions : dict):
    if(self.variable_volume.get(instructions['name'], None) != None):
        self.variable_volume[instructions['name']]['volumes'] = [-1]; # Since volumes is a list, we wrap our single volume data in its own list. This is to avoid any issues when reading a disposed variable's entry down the line
        self.variable_volume[instructions['name']]['size']    = 0;    # A disposed variable doesn't have a presence on the board. It's size is therefore zero.
    else:
        self.violation_found = True;
        print("Violation found! Cannot dispose of a variable that has not been declared")

    print("Handling dispose...")

def handle_mix(self, instructions : dict):
    print("Handling mix...")

def handle_split(self, instructions : dict):
    print("Handling split...")

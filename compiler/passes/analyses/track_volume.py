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
                    #print(type(i))
                    #print(i)
                    #print(i.defs)
                    #print(i.uses)
                    handle(self, i)

                    if (self.violation_found):
                        print("Exiting...")
                        break;

                    print(self.variable_volume)

            if (self.violation_found):
                        print("Exiting...")
                        break;

        return {'name': self.name, 'result': None} # Not sure what is going on here, but its needed to prevent a crash


def handle(self, instruction : IR): # The meat of the logic. Just ferries out the functions based on the type of instruction.
    if (type(instruction) == Dispense):
        handle_dispense(self, instruction)
        return

    if (type(instruction) == Dispose):
        handle_dispose(self, instruction)
        return

    if (type(instruction) == Mix):
        handle_mix(self, instruction)
        return

    if (type(instruction) == Split):
        handle_split(self, instruction)
        return





def handle_dispense(self, instructions : IR):
    print("Handling dispense...")
    quantity = 10; # This is the default value. I don't have a way of tracking custom volumes, so we will assume everything is default for now.

    # Initialize the structures we will use later on
    entry = dict() # The dict that will hold our new entry in the variable_volume ds
    volumes = list() # The list that will holds the volumes stored at each index

    volumes.append(quantity) # Add the dispense'd quantity toi the volumes list. In this case we assume that size is always 1, so we only do it a single time.

    # Build the entry dict
    entry['size'] = instructions.defs['size']
    entry['volumes'] = volumes

    # Add the entry to the volume tracker
    self.variable_volume[instructions.defs['name']] = entry

def handle_dispose(self, instructions : IR):
    print("Handling dispose...")
    if(self.variable_volume.get(instructions.defs['name'], None) != None):
        self.variable_volume[instructions.defs['name']]['volumes'] = [-1]; # Since volumes is a list, we wrap our single volume data in its own list. This is to avoid any issues when reading a disposed variable's entry down the line
        self.variable_volume[instructions.defs['name']]['size']    = 0;    # A disposed variable doesn't have a presence on the board. It's size is therefore zero.
    else:
        self.violation_found = True;
        print("Violation found! Cannot dispose of a variable that has not been declared")    

def handle_mix(self, instructions : IR):
    print("Handling mix...")

    # Quantities. This needs to be parsed from somewhere else, but the support doesn't exist. We will assume that the default value is requested for now.
    quantity_0 = 10 # The quantity of material 0 that is being mixed
    quantity_1 = 10 # The quantity of variable 1 that is being mixed

    if (instructions.uses[0]['offset'] >= 0):
        if (quantity_0 > self.variable_volume[instructions.uses[0]['name']]['volumes'][instructions.uses[0]['offset']]):
            self.violation_found = True;
            print("Violation found!")
            return
    else:
        if (quantity_0 > sum(self.variable_volume[instructions.uses[0]['name']]['volumes'])):
            self.violation_found = True;
            print("Violation found!")
            return

    if (instructions.uses[1]['offset'] >= 0):
        if (quantity_1 > self.variable_volume[instructions.uses[1]['name']]['volumes'][instructions.uses[1]['offset']]):
            self.violation_found = True;
            print("Violation found!")
            return

    else:
        if (quantity_1 > sum(self.variable_volume[instructions.uses[1]['name']]['volumes'])):
            self.violation_found = True;
            print("Violation found!")
            return

    #print("Mixing " + str(instructions.uses[0]['name']) + " and " + str(instructions.uses[1]['name']))

    # Initialize the structures we will use later on
    entry = dict() # The dict that will hold our new entry in the variable_volume ds
    volumes = list() # The list that will holds the volumes stored at each index

    volumes.append(quantity_0 + quantity_1) # Add the dispense'd quantity to the volumes list. In this case we assume that size is always 1, so we only do it a single time.

    # Build the entry dict
    entry['size'] = instructions.defs['size']
    entry['volumes'] = volumes

    # Add the entry to the volume tracker
    self.variable_volume[instructions.defs['name']] = entry

def handle_split(self, instructions : IR):
    print("Handling split...")

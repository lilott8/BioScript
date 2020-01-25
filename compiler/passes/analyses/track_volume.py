from copy import deepcopy

import networkx as nx

from compiler.data_structures import Program
from compiler.passes.analyses.bs_analysis import BSAnalysis
from compiler.data_structures.ir import *


class VolumeTracker(BSAnalysis):

    def __init__(self):
        super().__init__("Volume Tracking")  # Sets the name to Volume Tracking?
        self.variable_volume = dict()  # The dict that will store the current volumes of relevant variables
        self.past_volumes = []     # Stores all past states of volumes
        self.violation_found = False
        self._program = None;

    def analyze(self, program: Program) -> dict:  # The main function of the class

        self._program = program

        for root in program.functions:

            for node, data in program.bb_graph.nodes(data=True):

                for i in program.functions[root]['blocks'][node].instructions:

                    self.handle(i)

                    self.past_volumes.append(deepcopy(self.variable_volume)) # After every instruction has been handled, append the current state of the volume tracker to this list

                    if self.violation_found:
                        break;

            if self.violation_found:
                break;

        return {'name': self.name,
                'result': [self.violation_found, self.past_volumes]}  # Returns the relevant results

    def handle(self,
               instruction: IR):  # The meat of the logic. Just ferries out the functions based on the type of instruction.
        if type(instruction) == Dispense:
            self.handle_dispense(instruction)
            return

        if type(instruction) == Dispose:
            self.handle_dispose(instruction)
            return

        if type(instruction) == Mix:
            self.handle_mix(instruction)
            return

        if type(instruction) == Split:
            self.handle_split(instruction)
            return
        if type(instruction) == Phi:
            self.handle_phi(instruction)

    # We assume that the variable being created here has the minimum possible volume. This way, the compiler only proceeds when volume is guaranteed to be correct
    def handle_phi(self, instructions: IR):
        possible_volumes = []

        for i in range(len(instructions.uses)):

            possible_volumes.append(deepcopy(min(self.variable_volume[instructions.uses[i]]['volumes'])))

        entry = dict()  # The dict that will hold our new entry in the variable_volume ds
        volumes = list()  # The list that will holds the volumes stored at each index

        volumes.append(min(possible_volumes))  # Add the dispense'd quantity toi the volumes list. In this case we assume that size is always 1, so we only do it a single time.

        # Build the entry dict
        entry['size'] = 1
        entry['volumes'] = volumes

        # Add the entry to the volume tracker
        self.variable_volume[instructions.defs['name']] = entry

    def handle_dispense(self, instructions: IR):

        quantity = min(self._program.symbol_table.get_local(instructions.defs['name'], "main").volumes[instructions.iid])

        # Initialize the structures we will use later on
        entry = dict()  # The dict that will hold our new entry in the variable_volume ds
        volumes = list()  # The list that will holds the volumes stored at each index

        volumes.append(
            quantity)  # Add the dispense'd quantity toi the volumes list. In this case we assume that size is always 1, so we only do it a single time.

        # Build the entry dict
        entry['size'] = instructions.defs['size']
        entry['volumes'] = volumes

        # Add the entry to the volume tracker
        self.variable_volume[instructions.defs['name']] = entry

    def handle_dispose(self,
                       instructions: IR):  # This is the function that is called when a dispose instruction is found.

        if instructions.uses[0]['size'] < 1 or self.get_volume(instructions.uses[0]) < 1:
            self.violation_found = True
            return

        if instructions.uses[0]['offset'] >= 0:
            if self.variable_volume.get(instructions.defs['name'], None) is not None:
                self.variable_volume[instructions.defs['name']]['volumes'][instructions[
                    'offset']] = -1  # Since volumes is a list, we wrap our single volume data in its own list. This is to avoid any issues when reading a disposed variable's entry down the line

            else:
                self.violation_found = True
        else:
            self.variable_volume[instructions.defs['name']]['volumes'] = [
                -1]  # Since volumes is a list, we wrap our single volume data in its own list. This is to avoid any issues when reading a disposed variable's entry down the line
            self.variable_volume[instructions.defs['name']][
                'size'] = 0  # A disposed variable doesn't have a presence on the board. It's size is therefore zero.

    def _handle_dispose(self,
                        instructions: dict):  # This is an internal simulation of the proper dispose function. It is used internally by mix and split when the host variable(s) are destroyed by the execution of the instruction

        if instructions['offset'] >= 0:
            if self.variable_volume.get(instructions['name'], None) is not None:
                self.variable_volume[instructions['name']]['volumes'][instructions['offset']] = -1  # Since volumes is a list, we wrap our single volume data in its own list. This is to avoid any issues when reading a disposed variable's entry down the line
            else:
                self.violation_found = True

        else:
            self.variable_volume[instructions['name']]['volumes'] = [
                -1]  # Since volumes is a list, we wrap our single volume data in its own list. This is to avoid any issues when reading a disposed variable's entry down the line
            self.variable_volume[instructions['name']][
                'size'] = 0  # A disposed variable doesn't have a presence on the board. It's size is therefore zero.

    def handle_mix(self, instructions: IR):
        quantity = self._program.symbol_table.get_local(instructions.defs['name'], "main").volumes[instructions.iid]

        encoded_quantity = self._program.symbol_table.get_local(instructions.defs['name'], "main").value.volume['quantity'] # The quantity stored in an encoded float value.

        encoded_str = str(int(encoded_quantity)) # Convert to a string to make it easier to parse

        num_digits_a = int(encoded_str[0]) # Grab the digit marker for the first value
        num_digits_b = int(encoded_str[1]) # Grab the digit marker for the second value

        quantity_0 = quantity[0] # Grab the first value
        quantity_1 = quantity[1] # Grab the second value

        # Check if there is enough volume in the two uses to support the operation
        if instructions.uses[0]['offset'] >= 0:  # In this case, a discrete offset of 'volumes' is used. Therefore, the value of 'volumes['offset']' must be at least quantity_0
            if quantity_0 > self.variable_volume[instructions.uses[0]['name']]['volumes'][instructions.uses[0]['offset']]:
                self.violation_found = True
                return

        else:  # In this case, offset is -1. That means that we need to use every single drop in whichever index in 'volumes'. Therefore, the sumation of 'volumes' must be at least quantity_0.
            if quantity_0 > sum(self.variable_volume[instructions.uses[0]['name']]['volumes']):
                self.violation_found = True
                return

        # Perform the same checks for the other use
        if instructions.uses[1]['offset'] >= 0:
            if quantity_1 > self.variable_volume[instructions.uses[1]['name']]['volumes'][instructions.uses[1]['offset']]:
                self.violation_found = True
                return

        else:
            if quantity_1 > sum(self.variable_volume[instructions.uses[1]['name']]['volumes']):
                self.violation_found = True
                return

        # Initialize the structures we will use later on
        entry = dict()  # The dict that will hold our new entry in the variable_volume ds
        volumes = list()  # The list that will holds the volumes stored at each index

        volumes.append(quantity_0 + quantity_1)  # Add the dispense'd quantity to the volumes list. In this case we assume that size is always 1, so we only do it a single time.

        # Build the entry dict
        entry['size'] = instructions.defs['size']
        entry['volumes'] = volumes

        # Add the entry to the volume tracker
        self.variable_volume[instructions.defs['name']] = entry

        # Adjust the entries for the two variables that were used
        if quantity_0 == self.variable_volume[instructions.uses[0]['name']]['volumes'][instructions.uses[0]['offset']]:
            self._handle_dispose(instructions.uses[0]) # if the volume is completely used up, destroy the old var
        else:
            self.variable_volume[instructions.uses[0]['name']]['volumes'][instructions.uses[0]['offset']] -= quantity_0 # If the volume isn't totally used, simply reduce its volume appropriately

        if quantity_1 == self.variable_volume[instructions.uses[1]['name']]['volumes'][instructions.uses[1]['offset']]:
            self._handle_dispose(instructions.uses[1])
        else:
            self.variable_volume[instructions.uses[1]['name']]['volumes'][instructions.uses[1]['offset']] -= quantity_1

    def handle_split(self, instructions: IR):
        if self.get_volume(instructions.uses[0]) <= 0:
            self.violation_found = True
            return

        if self.get_volume(instructions.uses[0]) % instructions.defs['size'] != 0:
            self.violation_found = True
            return

        # Initialize the structures we will use later on
        entry = dict()  # The dict that will hold our new entry in the variable_volume ds
        volumes = list()  # The list that will holds the volumes stored at each index

        for i in range(instructions.defs[
                           'size']):  # Since a split should evenly break a variable into a given set of sub-variables, this loop puts volume/num_split of the use into each sub-variable of the def
            volumes.append(self.get_volume(instructions.uses[0]) / instructions.defs['size'])

        # Build the entry dict
        entry['size'] = instructions.defs['size']
        entry['volumes'] = volumes

        # Add the entry to the volume tracker
        self.variable_volume[instructions.defs['name']] = entry

        self._handle_dispose(instructions.uses[0])

    def get_volume(self,
                   var: dict) -> int:  # A helper function that fetch's the volume associated with a given variable's offset. This is not user-guarded, so use sparingly.
        if var['offset'] >= 0:
            return self.variable_volume[var['name']]['volumes'][var['offset']];
        else:
            return sum(self.variable_volume[var['name']]['volumes'])

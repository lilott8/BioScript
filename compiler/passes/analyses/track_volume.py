from copy import deepcopy
from compiler.data_structures import Program
from compiler.passes.analyses.bs_analysis import BSAnalysis
from compiler.data_structures.ir import *
from compiler.data_structures.variable import Number


class VolumeTracker(BSAnalysis):

    def __init__(self):
        super().__init__("Volume Tracking")  # Sets the name to Volume Tracking?
        self.variable_volume = dict()  # The dict that will store the current volumes of relevant variables
        self.past_volumes = []  # Stores all past states of volumes
        self.violation_found = False
        self._program = None
        self.in_conditional = False
        self.conditional_list = list()

    def analyze(self, program: Program) -> dict:  # The main function of the class

        self._program = program

        for root in program.functions:
            # if inlining, skip the other function roots
            if program.config.inline:
                if root != 'main':
                    continue

            for node, data in program.bb_graph.nodes(data=True):
                # if inlining, skip the other function data
                if program.config.inline:
                    if data:
                        if data['function'] != 'main':
                            continue
                    else:
                        continue
                if self.in_conditional and data:
                    #if hasattr(data, 'label'):
                    if len(data) == 1:
                        self.in_conditional = False
                    elif data['label'].startswith('bsbbif'):
                        if data['label'].endswith('j'):
                            self.in_conditional = False
                        if data['label'].endswith('f'):  # check that the next data label is not bsbbif_x_j and if so, the conditional has ended
                            if node + 1 not in program.bb_graph.nodes:
                                self.in_conditional = False
                            else:
                                if not program.bb_graph._node[node+1]['label'].endswith('j'):
                                    self.in_conditional = False

                for i in program.functions[root]['blocks'][node].instructions:
                    if self.violation_found:
                        break

                    self.handle(i)

                    self.past_volumes.append(deepcopy(self.variable_volume))  # After every instruction has been handled, append the current state of the volume tracker to this list

                    if self.violation_found:
                        break

            if self.violation_found:
                break

        return {'name': self.name,
                'result': [self.violation_found, self.past_volumes]}  # Returns the relevant results

    def handle(self,instruction: IR):  # The meat of the logic. Just ferries out the functions based on the type of instruction.
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

        if type(instruction) == Conditional:
            if instruction.left['name'].startswith('REPEAT') or instruction.right['name'].startswith('REPEAT'):  # found repeat conditional
                return
            self.handle_conditional(instruction)

    def handle_conditional(self, instructions: IR):
        self.in_conditional = True

    # We now keep every possible volume
    def handle_phi(self, instructions: IR):
        possible_volumes = list()
        size_save = 0
        # quick hack to ignore repeat instructions
        # TODO: A more robust method of handling repeats is needed as currently repeats are ignored,
        #  and the instructions located inside are checked only once
        #  If and else handling now works in volume tracking
        if isinstance(instructions.defs['var'].points_to.value, Number):
            return

        for i in range(len(instructions.uses)):
            #only utilize this use if valid
            if instructions.uses[i] not in self.variable_volume:
                continue
            if not self.variable_volume[instructions.uses[i]]['volumes']:
                continue

            for val in self.variable_volume[instructions.uses[i]]['volumes']:
                if self.variable_volume[instructions.uses[i]]['size'] > 1:
                    possible_volumes.append(deepcopy(val))
                    size_save = self.variable_volume[instructions.uses[i]]['size']
                elif deepcopy(val) not in possible_volumes:
                    possible_volumes.append(deepcopy(val))

            self.variable_volume[instructions.uses[i]]['volumes'] = [-1]
            self.variable_volume[instructions.uses[i]]['size'] = 0

        entry = dict()  # The dict that will hold our new entry in the variable_volume ds

        # Build the entry dict
        if size_save != 0:
            entry['size'] = size_save
        else:
            entry['size'] = 1
        # keep the actual possible volumes propagated
        entry['volumes'] = possible_volumes

        # Add the entry to the volume tracker
        self.variable_volume[instructions.defs['name']] = entry

    def handle_dispense(self, instructions: IR):

        quantity = min(self._program.symbol_table.get_local(instructions.defs['name'], "main").volumes[instructions.iid])

        # Initialize the structures we will use later on
        entry = dict()  # The dict that will hold our new entry in the variable_volume ds
        volumes = list()

        volumes.append(quantity)  # Add the dispense'd quantity toi the volumes list. In this case we assume that size is always 1, so we only do it a single time.

        # Build the entry dict
        entry['size'] = instructions.defs['size']
        entry['volumes'] = volumes

        # Add the entry to the volume tracker
        self.variable_volume[instructions.defs['name']] = entry

    def handle_dispose(self,instructions: IR):  # This is the function that is called when a dispose instruction is found.
        if instructions.uses[0]['offset'] < 0:
            if sum(self.variable_volume[instructions.defs['name']]['volumes']) < 1:
                self.violation_found = True
                return

        if instructions.uses[0]['size'] < 1 and sum(self.variable_volume[instructions.defs['name']]['volumes']) < 1:
            self.violation_found = True
            return

        vol_save = []
        size_save = 0
        num_unique_values = 1
        if self.in_conditional:
            vol_save = deepcopy(self.variable_volume[instructions.defs['name']]['volumes'])
            size_save = deepcopy(self.variable_volume[instructions.defs['name']]['size'])

        # handle the case of disposing a certain offset
        if instructions.uses[0]['offset'] >= 0:
            if self.variable_volume.get(instructions.defs['name'], None) is not None:
                unique_values_set = set()
                for i in self.variable_volume[instructions.defs['name']]['volumes']:
                    unique_values_set.add(i)
                num_unique_values = len(unique_values_set)
                if 0 in unique_values_set:
                    num_unique_values -= 1
                if -1 in unique_values_set:
                    num_unique_values -= 1
                k = 0
                for i in range(num_unique_values):
                    if self.variable_volume[instructions.defs['name']]['volumes'][instructions.uses[0]['offset'] + k] in {0, -1}:
                        self.violation_found = True
                        return
                    if self.in_conditional:
                        vol_save[instructions.uses[0]['offset'] + k] = 0
                    else:
                        self.variable_volume[instructions.defs['name']]['volumes'][instructions.uses[0]['offset'] + k] = -1
                    k += instructions.uses[0]['size']

            else:
                self.violation_found = True
        else:
            self.variable_volume[instructions.defs['name']]['volumes'] = [-1]  # Since volumes is a list, we wrap our single volume data in its own list. This is to avoid any issues when reading a disposed variable's entry down the line
            self.variable_volume[instructions.defs['name']]['size'] = 0  # A disposed variable doesn't have a presence on the board. It's size is therefore zero.

        if self.in_conditional and instructions.uses[0]['offset'] < 0:
            for i in range(len(self.variable_volume[instructions.defs['name']]['volumes'])):
                if self.variable_volume[instructions.defs['name']]['volumes'][i] == -1:
                    self.variable_volume[instructions.defs['name']]['volumes'][i] = 0
            for vol in vol_save:
                if vol not in self.variable_volume[instructions.defs['name']]['volumes']:
                    self.variable_volume[instructions.defs['name']]['volumes'].append(vol)
            if self.variable_volume[instructions.defs['name']]['size'] == 0:
                self.variable_volume[instructions.defs['name']]['size'] = size_save

        elif self.in_conditional:
            k = 0
            i = 0
            while i < num_unique_values:
                for index in range(self.variable_volume[instructions.defs['name']]['size']):
                    self.variable_volume[instructions.defs['name']]['volumes'].append(vol_save[index + k])
                k = k + self.variable_volume[instructions.defs['name']]['size']
                i += 1

    def _handle_dispose(self,
                        instructions: dict):  # This is an internal simulation of the proper dispose function. It is used internally by mix and split when the host variable(s) are destroyed by the execution of the instruction

        if instructions['offset'] >= 0:
            if self.variable_volume.get(instructions['name'], None) is not None:
                if self.in_conditional:
                    if 0 in self.variable_volume[instructions['name']]['volumes']:  # check to see if the entire thing should be disposed
                        self.variable_volume[instructions['name']]['volumes'] = [-1]
                        return
                    if 0 not in self.variable_volume[instructions['name']]['volumes']:
                        self.variable_volume[instructions['name']]['volumes'].append(0)
                        return
                self.variable_volume[instructions['name']]['volumes'] = [-1]
                if self.variable_volume[instructions['name']]['size'] == 1:
                    self.variable_volume[instructions['name']]['size'] = 0
            else:
                self.violation_found = True

        else:
            if self.in_conditional:
                if 0 in self.variable_volume[instructions['name']]['volumes']:  # check to see if the entire thing should be disposed
                    self.variable_volume[instructions['name']]['volumes'] = [-1]
                    return
                if 0 not in self.variable_volume[instructions['name']]['volumes']:
                    self.variable_volume[instructions['name']]['volumes'].append(0)
                    return
            self.variable_volume[instructions['name']]['volumes'] = [-1]  # Since volumes is a list, we wrap our single volume data in its own list. This is to avoid any issues when reading a disposed variable's entry down the line
            self.variable_volume[instructions['name']]['size'] = 0  # A disposed variable doesn't have a presence on the board. It's size is therefore zero.

    def handle_mix(self, instructions: IR):
        base = self._program.symbol_table.get_local(instructions.defs['name'], "main").volumes[instructions.iid]
        left_base = base[0]  # Grab the first base value
        right_base = base[1]  # Grab the second base value
        volumes = list()  # The list that will holds the volumes stored at each index
        copy_of_left_use_volume = 0
        copy_of_right_use_volume = 0
        left_base_used = 0
        left_not_default = 0
        right_base_used = 0
        right_not_default = 0

        # This means an actual specific volume was passed in to take from each use. Rather than just the defeault of the whole volume
        if left_base != 10:
            left_not_default = 1
        if right_base != 10:
            right_not_default = 1

        # The idea for this is to consolidate a split of muliple sizes and to consolidate mulitple broken up volumes to one value
        # So a split with [5, 5, 10, 10] should become [10, 20]
        # if its a split and has multiple components and is not an individual value
        if instructions.uses[0]['size'] > 1 and instructions.uses[0]['offset'] < 0:
            vol_sum = 0
            unique_values_set = set()
            for i in self.variable_volume[instructions.uses[0]['name']]['volumes']:
                unique_values_set.add(i)
            num_unique_values = len(unique_values_set)
            if 0 in unique_values_set:
                num_unique_values -= 1
            if -1 in unique_values_set:
                num_unique_values -= 1
            k = 0
            save_vol = list()
            for j in range(num_unique_values):
                for i in range(instructions.uses[0]['size']):
                    vol_sum += self.variable_volume[instructions.uses[0]['name']]['volumes'][i + k]
                if vol_sum not in save_vol:
                     save_vol.append(vol_sum)
                k += instructions.uses[0]['size']
                vol_sum = 0
            self.variable_volume[instructions.uses[0]['name']]['volumes'] = save_vol

        # do the same for the other use, in case it too, is a split
        # if its a split and has multiple components and is not an individual value
        if instructions.uses[1]['size'] > 1 and instructions.uses[1]['offset'] < 0:
            vol_sum = 0
            unique_values_set = set()
            for i in self.variable_volume[instructions.uses[1]['name']]['volumes']:
                unique_values_set.add(i)
            num_unique_values = len(unique_values_set)
            if 0 in unique_values_set:
                num_unique_values -= 1
            if -1 in unique_values_set:
                num_unique_values -= 1
            k = 0
            save_vol = list()
            for j in range(num_unique_values):
                for i in range(instructions.uses[1]['size']):
                    vol_sum += self.variable_volume[instructions.uses[1]['name']]['volumes'][i + k]
                if vol_sum not in save_vol:
                    save_vol.append(vol_sum)
                k += instructions.uses[1]['size']
                vol_sum = 0
            self.variable_volume[instructions.uses[1]['name']]['volumes'] = save_vol

        # Handle the case where both the left and right uses of the mix are single data for a multiple data instruction
        # Something like mix b[1] and c[2]
        if instructions.uses[0]['offset'] >= 0 and instructions.uses[1]['offset'] >= 0:
            copy_of_left_use_volume = deepcopy(self.variable_volume[instructions.uses[0]['name']]['volumes'])
            copy_of_right_use_volume = deepcopy(self.variable_volume[instructions.uses[1]['name']]['volumes'])
            unique_values_set1 = set()
            for i in self.variable_volume[instructions.uses[0]['name']]['volumes']:
                unique_values_set1.add(i)
            num_unique_values1 = len(unique_values_set1)
            if 0 in unique_values_set1:  # decrement if end val is found
                num_unique_values1 -= 1
            if -1 in unique_values_set1:  # decrement if end val is found
                num_unique_values1 -= 1
            unique_values_set2 = set()
            for i in self.variable_volume[instructions.uses[1]['name']]['volumes']:
                unique_values_set2.add(i)
            num_unique_values2 = len(unique_values_set2)
            if 0 in unique_values_set2:  # decrement if end val is found
                num_unique_values2 -= 1
            if -1 in unique_values_set2:  # decrement if end val is found
                num_unique_values2 -= 1
            k1 = 0
            for i in range(num_unique_values1):
                if instructions.uses[0]['offset'] + k1 >= len(self.variable_volume[instructions.uses[0]['name']]['volumes']):
                    continue
                k2 = 0
                for j in range(num_unique_values2):
                    if instructions.uses[1]['offset'] + k2 >= len(self.variable_volume[instructions.uses[1]['name']]['volumes']):
                        continue
                    quantity_0 = self.variable_volume[instructions.uses[0]['name']]['volumes'][instructions.uses[0]['offset'] + k1]
                    if quantity_0 <= 0:
                        if num_unique_values1 > 1:  # this means that there are values of -1 or 0, but there are other valid values
                            continue
                        self.violation_found = True
                        return
                    # add a check in case a specific mix volume was included
                    if left_base > quantity_0 and left_not_default == 1:
                        if instructions.uses[0]['name'] in self.conditional_list:
                            continue
                        self.violation_found = True
                        return
                    if left_base < quantity_0 and left_not_default == 1:
                        quantity_0 = left_base
                        left_base_used = 1
                    if left_base_used == 1:
                        if copy_of_left_use_volume[instructions.uses[0]['offset'] + k1] == self.variable_volume[instructions.uses[0]['name']]['volumes'][instructions.uses[0]['offset'] + k1]:
                            copy_of_left_use_volume[instructions.uses[0]['offset'] + k1] -= left_base
                    else:
                        if copy_of_left_use_volume[instructions.uses[0]['offset'] + k1] == self.variable_volume[instructions.uses[0]['name']]['volumes'][instructions.uses[0]['offset'] + k1]:
                            copy_of_left_use_volume[instructions.uses[0]['offset'] + k1] -= quantity_0  # allow the volume to be reset for this index later
                    quantity_1 = self.variable_volume[instructions.uses[1]['name']]['volumes'][instructions.uses[1]['offset'] + k2]
                    if quantity_1 <= 0:
                        if num_unique_values2 > 1:  # this means that there are values of -1 or 0, but there are other valid values
                            continue
                        self.violation_found = True
                        return
                    # add a check in case a specific mix volume was included
                    if right_base > quantity_1 and right_not_default == 1:
                        if instructions.uses[1]['name'] in self.conditional_list:
                            continue
                        self.violation_found = True
                        return
                    if right_base < quantity_1 and right_not_default == 1:
                        quantity_1 = right_base
                        right_base_used = 1
                    if right_base_used == 1:
                        if copy_of_right_use_volume[instructions.uses[1]['offset'] + k2] == self.variable_volume[instructions.uses[1]['name']]['volumes'][instructions.uses[1]['offset'] + k2]:
                            copy_of_right_use_volume[instructions.uses[1]['offset'] + k2] -= right_base
                    else:
                        if copy_of_right_use_volume[instructions.uses[1]['offset'] + k2] == self.variable_volume[instructions.uses[1]['name']]['volumes'][instructions.uses[1]['offset'] + k2]:
                            copy_of_right_use_volume[instructions.uses[1]['offset'] + k2] -= quantity_1  # allow the volume to be reset for this index later

                    if quantity_0 + quantity_1 not in volumes:  # treat as a set
                        volumes.append(quantity_0 + quantity_1)
                    k2 += instructions.uses[1]['size']
                k1 += instructions.uses[0]['size']

        # Handle the case where only the left use is a single data for a multiple data instruction
        # Something like mix b[1] and c
        elif instructions.uses[0]['offset'] >= 0 and instructions.uses[1]['offset'] < 0:
            copy_of_left_use_volume = deepcopy(self.variable_volume[instructions.uses[0]['name']]['volumes'])
            unique_values_set1 = set()
            for i in self.variable_volume[instructions.uses[0]['name']]['volumes']:
                unique_values_set1.add(i)
            num_unique_values1 = len(unique_values_set1)
            if 0 in unique_values_set1:  # decrement if end val is found
                num_unique_values1 -= 1
            if -1 in unique_values_set1:  # decrement if end val is found
                num_unique_values1 -= 1
            k1 = 0
            for i in range(num_unique_values1):
                if instructions.uses[0]['offset'] + k1 >= len(self.variable_volume[instructions.uses[0]['name']]['volumes']):
                    continue
                for right_vol in self.variable_volume[instructions.uses[1]['name']]['volumes']:
                    quantity_0 = self.variable_volume[instructions.uses[0]['name']]['volumes'][instructions.uses[0]['offset'] + k1]
                    if quantity_0 <= 0:
                        if num_unique_values1 > 1:  # this means that there are values of -1 or 0, but there are other valid values
                            continue
                        self.violation_found = True
                        return
                    if left_base > quantity_0 and left_not_default == 1:
                        self.violation_found = True
                        return
                    if left_base < quantity_0 and left_not_default == 1:
                        quantity_0 = left_base
                        left_base_used = 1
                    if left_base_used == 1:
                        if copy_of_left_use_volume[instructions.uses[0]['offset'] + k1] == self.variable_volume[instructions.uses[0]['name']]['volumes'][instructions.uses[0]['offset'] + k1]:
                            copy_of_left_use_volume[instructions.uses[0]['offset'] + k1] -= left_base
                    else:
                        copy_of_left_use_volume[instructions.uses[0]['offset'] + k1] -= quantity_0  # allow the volume to be reset for this index later
                    quantity_1 = right_vol
                    if quantity_1 <= 0:
                        if len(self.variable_volume[instructions.uses[1]['name']]['volumes']) > 1:  # this means that there are values of -1 or 0, but there are other valid values
                            continue
                        self.violation_found = True
                        return
                    if right_base > right_vol and right_not_default == 1:
                        if instructions.uses[1]['name'] in self.conditional_list:
                            continue
                        self.violation_found = True
                        return
                    if right_base < right_vol and right_not_default == 1:
                        quantity_1 = right_base
                        right_base_used = 1
                    if quantity_0 + quantity_1 not in volumes:  # treat as a set
                        volumes.append(quantity_0 + quantity_1)
                k1 += instructions.uses[0]['size']

        # Handle the case where only the right use is a single data for a multiple data instruction
        # Something like mix b and c[2]
        elif instructions.uses[0]['offset'] < 0 and instructions.uses[1]['offset'] >= 0:
            copy_of_right_use_volume = deepcopy(self.variable_volume[instructions.uses[1]['name']]['volumes'])
            unique_values_set2 = set()
            for i in self.variable_volume[instructions.uses[1]['name']]['volumes']:
                unique_values_set2.add(i)
            num_unique_values2 = len(unique_values_set2)
            if 0 in unique_values_set2:  # decrement if end val is found
                num_unique_values2 -= 1
            if -1 in unique_values_set2:  # decrement if end val is found
                num_unique_values2 -= 1
            k2 = 0
            for i in range(num_unique_values2):
                if instructions.uses[1]['offset'] + k2 >= len(self.variable_volume[instructions.uses[1]['name']]['volumes']):
                    continue
                for left_vol in self.variable_volume[instructions.uses[0]['name']]['volumes']:
                    quantity_0 = self.variable_volume[instructions.uses[1]['name']]['volumes'][instructions.uses[1]['offset'] + k2]
                    if quantity_0 <= 0:
                        if num_unique_values2 > 1:  # this means that there are values of -1 or 0, but there are other valid values
                            continue
                        self.violation_found = True
                        return
                    if right_base > quantity_0 and right_not_default == 1:
                        self.violation_found = True
                        return
                    if right_base < quantity_0 and right_not_default == 1:
                        quantity_0 = right_base
                        right_base_used = 1
                    if right_base_used == 1:
                        if copy_of_right_use_volume[instructions.uses[1]['offset'] + k2] == self.variable_volume[instructions.uses[1]['name']]['volumes'][instructions.uses[1]['offset'] + k2]:
                            copy_of_right_use_volume[instructions.uses[1]['offset'] + k2] -= right_base
                    else:
                        copy_of_right_use_volume[instructions.uses[1]['offset'] + k2] -= quantity_0  # allow the volume to be reset for this index later
                    quantity_1 = left_vol
                    if quantity_1 <= 0:
                        if len(self.variable_volume[instructions.uses[0]['name']]['volumes']) > 1:  # this means that there are values of -1 or 0, but there are other valid values
                            continue
                        self.violation_found = True
                        return
                    if left_base > left_vol and left_not_default == 1:
                        if instructions.uses[0]['name'] in self.conditional_list:
                            continue
                        self.violation_found = True
                        return
                    if left_base < left_vol and left_not_default == 1:
                        quantity_1 = left_base
                        left_base_used = 1
                    if quantity_0 + quantity_1 not in volumes:  # treat as a set
                        volumes.append(quantity_0 + quantity_1)
                k2 += instructions.uses[1]['size']

        # Handle the case where neither side of the uses is single data for a multiple data instruction
        # Something like mix b and c
        else:
            for left_vol in self.variable_volume[instructions.uses[0]['name']]['volumes']:
                for right_vol in self.variable_volume[instructions.uses[1]['name']]['volumes']:
                    quantity_0 = left_vol
                    quantity_1 = right_vol
                    if quantity_0 <= 0:
                        if len(self.variable_volume[instructions.uses[0]['name']]['volumes']) > 1:  # this means that there are values of -1 or 0, but there are other valid values
                            continue
                        self.violation_found = True
                        return
                    if quantity_1 <= 0:  # had to separate them
                        if len(self.variable_volume[instructions.uses[1]['name']]['volumes']) > 1:  # this means that there are values of -1 or 0, but there are other valid values
                            continue
                        self.violation_found = True
                        return
                    # add a check in case a specific mix volume was included
                    if left_base > left_vol and left_not_default == 1:
                        if instructions.uses[0]['name'] in self.conditional_list:
                            continue
                        self.violation_found = True
                        return
                    if left_base < left_vol and left_not_default == 1:
                        quantity_0 = left_base
                        left_base_used = 1
                    if right_base > right_vol and right_not_default == 1:
                        if instructions.uses[1]['name'] in self.conditional_list:
                            continue
                        self.violation_found = True
                        return
                    if right_base < right_vol and right_not_default == 1:
                        quantity_1 = right_base
                        right_base_used = 1
                    if quantity_0 + quantity_1 not in volumes:  # treat as a set
                        volumes.append(quantity_0 + quantity_1)

        # Initialize the structures we will use later on
        entry = dict()  # The dict that will hold our new entry in the variable_volume ds

        # Build the entry dict
        entry['size'] = instructions.defs['size']
        entry['volumes'] = volumes

        # Add the entry to the volume tracker
        self.variable_volume[instructions.defs['name']] = entry

        # unique volume situation if both sides of the mix are the same instruction i.e  c = mix(b1[0], b1[1])
        # if both are parts of the same instruction, then the volume is shared
        if instructions.uses[0]['name'] == instructions.uses[1]['name']:
            if instructions.uses[0]['offset'] >= 0 and instructions.uses[1]['offset'] >= 0:
                stored_volumes = deepcopy(self.variable_volume[instructions.uses[0]['name']]['volumes'])
                volume_conditional_save = deepcopy(self.variable_volume[instructions.uses[0]['name']]['volumes'])
                for i in range(len(self.variable_volume[instructions.uses[0]['name']]['volumes'])):
                    if copy_of_left_use_volume[i] != stored_volumes[i]:
                        self.variable_volume[instructions.uses[0]['name']]['volumes'][i] = copy_of_left_use_volume[i]
                    if copy_of_right_use_volume[i] != stored_volumes[i]:
                        self.variable_volume[instructions.uses[0]['name']]['volumes'][i] = copy_of_right_use_volume[i]
                if self.in_conditional:
                    for vol in self.variable_volume[instructions.uses[0]['name']]['volumes']:
                        volume_conditional_save.append(vol)
                    self.variable_volume[instructions.uses[0]['name']]['volumes'] = volume_conditional_save
                self.variable_volume[instructions.uses[1]['name']]['volumes'] = self.variable_volume[instructions.uses[0]['name']]['volumes']  # set both to be the same
                return

        if instructions.uses[0]['offset'] >= 0:
            if self.in_conditional:
                if instructions.uses[0]['name'] not in self.conditional_list:
                    self.conditional_list.append(instructions.uses[0]['name'])
                    for val in copy_of_left_use_volume:
                       self.variable_volume[instructions.uses[0]['name']]['volumes'].append(val)
                else:
                    for i in range(len(copy_of_left_use_volume)):
                        if i < instructions.uses[0]['size']:
                            self.variable_volume[instructions.uses[0]['name']]['volumes'].append(copy_of_left_use_volume[i])
            else:
                self.variable_volume[instructions.uses[0]['name']]['volumes'] = copy_of_left_use_volume
        else:
            if left_base_used == 1:  # in the event that the whole instruction is being used, but only a specified volume, subtract this volume from each index
                for i in range(len(deepcopy(self.variable_volume[instructions.uses[0]['name']]['volumes']))):
                    if self.in_conditional:
                        if instructions.uses[0]['name'] not in self.conditional_list:
                            self.conditional_list.append(instructions.uses[0]['name'])
                            if self.variable_volume[instructions.uses[0]['name']]['volumes'][i] - left_base not in self.variable_volume[instructions.uses[0]['name']]['volumes']:
                                self.variable_volume[instructions.uses[0]['name']]['volumes'].append(self.variable_volume[instructions.uses[0]['name']]['volumes'][i] - left_base)
                        else:
                            if self.variable_volume[instructions.uses[0]['name']]['volumes'][i] != self.variable_volume[instructions.uses[0]['name']]['volumes'][0]:
                                continue
                            if self.variable_volume[instructions.uses[0]['name']]['volumes'][i] - left_base not in self.variable_volume[instructions.uses[0]['name']]['volumes']:
                                self.variable_volume[instructions.uses[0]['name']]['volumes'].append(self.variable_volume[instructions.uses[0]['name']]['volumes'][i] - left_base)
                    else:
                        self.variable_volume[instructions.uses[0]['name']]['volumes'][i] -= left_base
            else:
                self._handle_dispose(instructions.uses[0])

        if instructions.uses[1]['offset'] >= 0:
            if self.in_conditional:
                if instructions.uses[1]['name'] not in self.conditional_list:
                    self.conditional_list.append(instructions.uses[1]['name'])
                    for val in copy_of_right_use_volume:
                        self.variable_volume[instructions.uses[1]['name']]['volumes'].append(val)
                else:
                    for i in range(len(copy_of_right_use_volume)):
                        if i < instructions.uses[1]['size']:
                            self.variable_volume[instructions.uses[1]['name']]['volumes'].append(copy_of_right_use_volume[i])
            else:
                self.variable_volume[instructions.uses[1]['name']]['volumes'] = copy_of_right_use_volume
        else:
            if right_base_used == 1:  # in the event that the whole instruction is being used, but only a specified volume, subtract this volume from each index
                for i in range(len(deepcopy(self.variable_volume[instructions.uses[1]['name']]['volumes']))):
                    if self.in_conditional:
                        if instructions.uses[1]['name'] not in self.conditional_list:
                            self.conditional_list.append(instructions.uses[1]['name'])
                            if self.variable_volume[instructions.uses[1]['name']]['volumes'][i] - right_base not in self.variable_volume[instructions.uses[1]['name']]['volumes']:
                               self.variable_volume[instructions.uses[1]['name']]['volumes'].append(self.variable_volume[instructions.uses[1]['name']]['volumes'][i] - right_base)
                        else:
                            if self.variable_volume[instructions.uses[1]['name']]['volumes'][i] != self.variable_volume[instructions.uses[1]['name']]['volumes'][0]:
                                continue
                            if self.variable_volume[instructions.uses[1]['name']]['volumes'][i] - right_base not in self.variable_volume[instructions.uses[1]['name']]['volumes']:
                               self.variable_volume[instructions.uses[1]['name']]['volumes'].append(self.variable_volume[instructions.uses[1]['name']]['volumes'][i] - right_base)
                    else:
                        self.variable_volume[instructions.uses[1]['name']]['volumes'][i] -= right_base
            else:
                self._handle_dispose(instructions.uses[1])

    def handle_split(self, instructions: IR):
        # Initialize the structures we will use later on
        entry = dict()  # The dict that will hold our new entry in the variable_volume ds
        volumes = list()  # The list that will holds the volumes stored at each index
        cond_save = 0

        # handle the situation when a single droplet from a multiple data instruction is then split
        if instructions.uses[0]['offset'] >= 0 and instructions.uses[0]['size'] > 1:
            vols_to_split = list()
            unique_values_set = set()
            for i in self.variable_volume[instructions.uses[0]['name']]['volumes']:
                unique_values_set.add(i)
            num_unique_values = len(unique_values_set)
            if 0 in unique_values_set:  # decrement if end val is found
                num_unique_values -= 1
            if -1 in unique_values_set:  # decrement if end val is found
                num_unique_values -= 1
            k = 0
            if self.in_conditional:
                cond_save = deepcopy(self.variable_volume[instructions.uses[0]['name']]['volumes'])
            for i in range(num_unique_values):
                vols_to_split.append(self.variable_volume[instructions.uses[0]['name']]['volumes'][instructions.uses[0]['offset'] + k])
                # set index entry to 0
                if self.in_conditional:
                    cond_save[instructions.uses[0]['offset'] + k] -= self.variable_volume[instructions.uses[0]['name']]['volumes'][instructions.uses[0]['offset'] + k]
                else:
                     self.variable_volume[instructions.uses[0]['name']]['volumes'][instructions.uses[0]['offset'] + k] -= self.variable_volume[instructions.uses[0]['name']]['volumes'][instructions.uses[0]['offset'] + k]
                k += instructions.uses[0]['size']
            for vol in vols_to_split:
                if vol <= 0:
                    self.violation_found = True
                    return
                # Since a split should evenly break a variable into a given set of sub-variables, this loop puts volume/num_split of the use into each sub-variable of the def
                for i in range(instructions.defs['size']):
                    volumes.append(vol / instructions.defs['size'])

        else:
            for vol in self.variable_volume[instructions.uses[0]['name']]['volumes']:
                if vol <= 0:
                    self.violation_found = True
                    return
                # Since a split should evenly break a variable into a given set of sub-variables, this loop puts volume/num_split of the use into each sub-variable of the def
                for i in range(instructions.defs['size']):
                    volumes.append(vol / instructions.defs['size'])

        # Build the entry dict
        entry['size'] = instructions.defs['size']
        entry['volumes'] = volumes

        # Add the entry to the volume tracker
        self.variable_volume[instructions.defs['name']] = entry

        if instructions.uses[0]['offset'] >= 0 and instructions.uses[0]['size'] > 1:
            if self.in_conditional:
                k = 0
                i = 0
                while i < num_unique_values:
                    for index in range(self.variable_volume[instructions.defs['name']]['size']):
                        self.variable_volume[instructions.uses[0]['name']]['volumes'].append(cond_save[index + k])
                    k = k + self.variable_volume[instructions.uses[0]['name']]['size']
                    i += 1
            return  # this case was already handled earlier
        self._handle_dispose(instructions.uses[0])

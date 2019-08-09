from compiler.data_structures import program as prog
from compiler.data_structures.ir import IRInstruction as iri
from compiler.data_structures.ir import InstructionSet
from compiler.data_structures.writable import Writable
from compiler.targets.base_target import BaseTarget


class IRTarget(BaseTarget):

    def __init__(self, program: prog.Program, name="IRTarget"):
        super().__init__(program, name)
        self.compiled = ""
        self.tab = ""
        self.tab_count = 0

    def increment_tab(self):
        self.tab_count += 1
        self.tab += "\t"

    def decrement_tab(self):
        self.tab_count -= 1
        if self.tab_count < 0:
            self.tab_count = 0
        self.tab = "".join("\t" for x in range(self.tab_count))

    def transform(self):
        for root in self.program.functions:
            for nid, block in self.program.functions[root]['blocks'].items():
                self.compiled += block.label + ":\n"
                self.increment_tab()
                for instruction in block.instructions:
                    self.compiled += self.tab
                    if instruction.op in InstructionSet.assignment:
                        # There is only one def.
                        self.compiled += "{}[{}] = {}(".format(instruction.defs['name'],
                                                               instruction.defs['offset'], instruction.op.name.lower())
                        # Grab the uses.
                        for use in instruction.uses:
                            if self.program.symbol_table.is_global(use['name']):
                                self.compiled += use['name'] + ", "
                            else:
                                self.compiled += "{}[{}], ".format(use['name'], use['offset'])
                        # Get rid of trailing characters
                        self.compiled = self.compiled[:-2]
                        self.compiled += ")"

                    elif instruction.op == iri.HEAT:
                        self.compiled += "{}({}[{}])".format(instruction.op.name.lower(), instruction.uses[0]['name'],
                                                             instruction.uses[0]['offset'])

                    # Add any meta operations.
                    if instruction.meta:
                        for meta in instruction.meta:
                            self.compiled += " @ {}{}".format(meta.quantity, meta.unit.name)

                    self.compiled += "\n"
                self.decrement_tab()

        self.program.write[self.program.name] = Writable(self.program.name,
                                                         "{}/{}.ir".format(self.config.output, self.program.name),
                                                         self.compiled)

    def write_mix(self) -> str:
        pass

    def write_split(self) -> str:
        pass

    def write_detect(self) -> str:
        pass

    def write_dispose(self) -> str:
        pass

    def write_dispense(self) -> str:
        pass

    def write_expression(self) -> str:
        pass

    def write_branch(self) -> str:
        pass

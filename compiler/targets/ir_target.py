from compiler.data_structures import program as prog
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
        self.tab = "".join("\t" for x in range(self.tab_count))

    def transform(self):

        for root in self.program.functions:
            for nid, block in self.program.functions[root]['blocks'].items():
                for instruction in block.instructions:
                    self.compiled += "{}\n".format(instruction)

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

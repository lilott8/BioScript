from compiler.data_structures.program import Program
from compiler.passes.transforms.bs_transform import BSTransform


class SIMDExpansion(BSTransform):

    def __init__(self):
        super().__init__("SIMD Expansion")

    def transform(self, program: Program) -> Program:
        for root in program.functions:
            for nid, block in program.functions[root]['blocks'].items():
                expanded_instructions = list()
                for x, instruction in enumerate(block.instructions):
                    for expanded in instruction.expand():
                        expanded_instructions.append(expanded)

                    self.log.info(instruction)
                block.instructions = expanded_instructions
        return program
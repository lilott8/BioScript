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
                    expanded_instructions.extend(instruction.expand())
                block.instructions = expanded_instructions
        return program
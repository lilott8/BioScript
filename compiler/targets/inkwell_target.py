from collections import deque

from compiler.data_structures import Program
from compiler.targets.base_target import BaseTarget


class InkwellTarget(BaseTarget):

    def __init__(self, configuration: 'Config'):
        super().__init__(configuration, "InkwellTarget")

    def transform(self, program: Program):
        queue = deque()
        queue.append(program.functions['main']['entry'])
        while queue:
            block = queue.popleft()
            self.log.info("Exploring block: " + str(block))
            for node, edge in program.bb_graph.out_edges(block):
                queue.append(edge)
            for instruction in program.functions['main']['blocks'][block].instructions:
                self.log.debug(instruction)

        return False

from compiler.targets.base_target import BaseTarget
from compiler.data_structures import BasicBlock
from collections import deque


class MFSimTarget(BaseTarget):

    def __init__(self, program):
        super().__init__(program, "MFSimTarget")

    def write_cfg(self):
        return False

    def write_dag(self, bb: BasicBlock):

        return False

    def transform(self):
        self.log.debug("MFSimTarget not yet implemented!")
        sequences = dict()
        for root in self.program.functions:
            sequences[root] = dict()
            for bid, block in self.program.functions[root]['blocks'].items():
                queue = deque()
                globalz = dict()

                # This gets all the nodes with no incoming edges
                # These are the source nodes of a graph.
                # This is an initialization step.
                for node in block.dag.nodes:
                    if len(block.dag.in_edges(node)) == 0:
                        queue.append(node)

                # A dictionary of the nodes and their associated data.
                graph = dict(block.dag.nodes('data'))

                print('here')

        print('here')
        return False

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

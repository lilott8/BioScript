from compiler.targets.base_target import BaseTarget
from compiler.data_structures import BasicBlock
from compiler.data_structures import IRInstruction
from collections import deque
import networkx as nx


class MFSimTarget(BaseTarget):

    def __init__(self, program):
        super().__init__(program, "MFSimTarget")
        self.cfg = dict()

    def build_cfg(self):
        for root in self.program.functions:
            leafs = set()
            tags = dict()
            self.dags[root] = dict()
            for bid, block in self.program.functions[root]['blocks'].items():
                if not block.instructions:
                    continue
                self.cfg[bid] = dict()
                curr = self.cfg[bid]
                write = True
                dag = nx.DiGraph()
                for instruction in block.instructions:
                    # self.log.info(instruction)

                    if instruction.op is IRInstruction.CONDITIONAL:
                        if len(block.instructions) is 1:
                            write = False

                        true_label = instruction.true_branch.label
                        false_label = instruction.false_branch.label

                        for bbid, bblock in self.program.functions[root]['blocks'].items():
                            if bblock.instructions and bblock.label:
                                if bblock.label.label is true_label:
                                    true_block = bbid
                                elif bblock.label.label is false_label:
                                    false_block = bbid
                                continue

                        curr[instruction.iid] = dict()
                        curr[instruction.iid] = {'f': false_block,
                                                     't': true_block}
                        if instruction.left.name.startswith("REPEAT"):
                            curr[instruction.iid]['c'] = 'repeat'
                            curr[instruction.iid]['repeat'] = instruction.left.value
                        else:  # could be nested conditional
                            curr[instruction.iid]['c'] = instruction.relop
                            self.log.warn("TEST non-repeat CONDITIONALS")


                    elif hasattr(instruction, 'uses'):
                        # Case x = op y (dispense, heat, dispose, store)
                        if len(instruction.uses) == 1:
                            # Look at the r-value.
                            use = next(iter(instruction.uses))
                            if use not in leafs:
                                dag.add_node(use.name, type="variable")
                                leafs.add(use.name)
                                leaf = use.name
                            else:
                                leaf = use.name
                            # Do the same thing, except for the l-value.
                            if instruction.defs:
                                if instruction.defs.name not in tags:
                                    dag.add_node(leaf, iid=instruction.iid, op=instruction.op.name, type="register")
                                    var_def = instruction.defs.name
                                    tags[instruction.defs.name] = var_def
                                else:
                                    var_def = instruction.defs.name
                                dag.add_edge(leaf, var_def)
                        else:
                            # Case x = y op z (mix, split, arithmetic)
                            var_def = instruction.defs.name
                            dag.add_node(var_def, iid=instruction.iid, op=instruction.op.name, type="register")
                            tags[var_def] = var_def
                            for use in instruction.uses:
                                leaf = use.name
                                if leaf not in leafs:
                                    dag.add_node(leaf, type="variable")
                                    leafs.add(leaf)
                                dag.add_edge(leaf, var_def)
                if write:
                    self.program.functions[root]['blocks'][bid].dag = dag
                    self.dags[root][bid] = dag
        return False

    def write_dag(self):
        return False

    def write_cfg(self):
        return False

    def transform(self):
        self.build_cfg()
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
                if block.dag is not None:
                    for node in block.dag.nodes:
                        if len(block.dag.in_edges(node)) == 0:
                            queue.append(node)
                else:
                    continue

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

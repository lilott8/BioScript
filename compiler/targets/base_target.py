import abc

import colorlog

import compiler.data_structures.program as prog
from shared.bs_exceptions import UndefinedException


class BaseTarget(metaclass=abc.ABCMeta):

    def __init__(self, program: prog.Program, name="BaseTarget"):
        self.log = colorlog.getLogger(self.__class__.__name__)
        self.program = program
        self.config = program.config
        self.name = name
        self.dags = dict()
        self.build_dags()

    def build_dags(self):
        """
        This is the classic Instruction Selection DAG algorithm.
        :return:
        """
        # for root in self.program.functions:
        #     self.dags[root] = dict()
        #     # Set of output variables seen in the DAG.
        #     leafs = set()
        #     # This maps an output variable (key) to a node in the graph.
        #     tags = dict()
        #     for nid, block in self.program.functions[root]['blocks'].items():
        #         graph = nx.DiGraph()
        #         # Op nodes are defined as {output var, op}
        #         # Var nodes are defined as {var}
        #         for instruction in block.instructions:
        #             # self.log.info(instruction)
        #             # Case x = op y (dispense, heat, dispose, store)
        #             if len(instruction.uses) == 1:
        #                 # Look at the r-value.  This does
        #                 # that without altering the set.
        #                 use = next(iter(instruction.uses))
        #                 if use not in leafs:
        #                     graph.add_node(use.name, type="variable")
        #                     leafs.add(use.name)
        #                     leaf = use.name
        #                 else:
        #                     leaf = use.name
        #                 # Do the same thing, except for the l-value.
        #                 if instruction.defs:
        #                     if instruction.defs.name not in tags:
        #                         graph.add_node(leaf, iid=instruction.iid, op=instruction.op.name, type="register")
        #                         var_def = instruction.defs.name
        #                         tags[instruction.defs.name] = var_def
        #                     else:
        #                         var_def = instruction.defs.name
        #                     graph.add_edge(leaf, var_def)
        #             else:
        #                 # Case x = y op z (mix, split)
        #                 var_def = instruction.defs.name
        #                 graph.add_node(var_def, iid=instruction.iid, op=instruction.op.name, type="register")
        #                 tags[var_def] = var_def
        #                 for use in instruction.uses:
        #                     leaf = use.name
        #                     if leaf not in leafs:
        #                         graph.add_node(leaf, type="variable")
        #                         leafs.add(leaf)
        #                     graph.add_edge(leaf, var_def)
        #         self.write_graph(graph)
        #         self.program.functions[root]['blocks'][nid].dag = graph
        #         self.dags[root][nid] = graph
        pass


    @staticmethod
    def get_safe_name(name: str) -> str:
        """
        Unified manner to create program-safe names
        :param name: Name of unsafe variable.
        :return: Safe name.
        """
        return name.replace(" ", "_").replace("-", "_")

    @abc.abstractmethod
    def transform(self):
        if self.config is None:
            raise UndefinedException("Config must be set before you can transform")
        pass

    @abc.abstractmethod
    def write_mix(self) -> str:
        pass

    @abc.abstractmethod
    def write_split(self) -> str:
        pass

    @abc.abstractmethod
    def write_detect(self) -> str:
        pass

    @abc.abstractmethod
    def write_dispose(self) -> str:
        pass

    @abc.abstractmethod
    def write_dispense(self) -> str:
        pass

    @abc.abstractmethod
    def write_expression(self) -> str:
        pass

    @abc.abstractmethod
    def write_branch(self) -> str:
        pass

import colorlog
import networkx as nx

from compiler.data_structures.program import Program
from compiler.passes.analyses.call_graph import CallGraph
from compiler.passes.transforms.split_edges import SplitEdges
from compiler.passes.transforms.ssa import SSA


class PassManager(object):

    def __init__(self, program: Program):
        self.config = None
        self.log = colorlog.getLogger(self.__class__.__name__)
        self.log.debug("Initializing pass manager.")
        self.program = program
        self.dependencies = {'analysis': nx.DiGraph(), 'transforms': nx.DiGraph()}
        self.transforms = dict()
        self.analysis = dict()
        self.init_analysis()
        self.init_transforms()
        # Ensure SSA is run first.
        self.run_ssa()

    def run_ssa(self):
        if not self.program.ssa_form:
            ssa = SSA()
            self.program = ssa.transform(self.program)
            self.program.ssa_form = True

            # self.log.info(self.program.functions['main']['blocks'])
            # self.log.info(self.program.symbol_table)

    def run_transformations(self):
        # TODO: Make this handle dependencies correctly.
        for key, value in self.transforms.items():
            self.program = value.transform(self.program)

    def run_analysis(self):
        for key, value in self.analysis.items():
            self.program.analysis[key] = value.analyze(self.program)

    def init_analysis(self):
        self.analysis['call_graph'] = CallGraph()
        self.dependencies['analysis'].add_node('call_graph')

    def init_transforms(self):
        self.transforms['split_edges'] = SplitEdges()
        self.dependencies['transforms'].add_node('split_edges')

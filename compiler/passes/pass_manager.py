import colorlog
import networkx as nx

from compiler.data_structures.program import Program
from compiler.passes.analyses.call_graph import CallGraph
from compiler.passes.analyses.slicer import Slicer
from compiler.passes.analyses.def_use import DefUseChains
from compiler.passes.transforms.inline import Inline
from compiler.passes.transforms.split_edges import SplitEdges
from compiler.passes.transforms.simd_expansion import SIMDExpansion
from compiler.passes.transforms.ssa import SSA


class PassManager(object):

    def __init__(self, program: Program):
        self.config = None
        self.log = colorlog.getLogger(self.__class__.__name__)
        self.log.debug("Initializing pass manager.")
        self.program = program
        self.config = program.config
        # self.dependencies = {'analysis': nx.DiGraph(), 'transforms': nx.DiGraph()}
        self.transforms = dict()
        self.analysis = dict()
        # Ensure SSA is run first.
        self.run_ssa()

    def run_ssa(self):
        if not self.program.ssa_form:
            ssa = SSA()
            self.program = ssa.transform(self.program)
            self.program.ssa_form = True
            # self.log.info(self.program.symbol_table)
            # self.log.info(self.program.functions['main']['blocks'])

    def run_transformations(self):
        self.init_transforms()
        # TODO: This should be handled through decorator.
        # TODO: Make this handle dependencies correctly.
        for key, value in self.transforms.items():
            if key is 'loop_unroll' and not self.config.loopunroll:
                continue
            self.program = value.transform(self.program)

    def run_analysis(self):
        self.init_analysis()
        # TODO: This should be handled through decorator.
        for key, value in self.analysis.items():
            self.program.analysis[key] = value.analyze(self.program)['result']

    def init_analysis(self):
        self.analysis['call_graph'] = CallGraph()
        self.analysis['def_use'] = DefUseChains()
        self.analysis['slicer'] = Slicer()
        # self.dependencies['analysis'].add_node('call_graph')

    def init_transforms(self):
        if self.config.inline:
            self.transforms['inline'] = Inline()
        self.transforms['split_edges'] = SplitEdges()
        self.transforms['simd_expansion'] = SIMDExpansion()
        # self.dependencies['transforms'].add_node('split_edges')

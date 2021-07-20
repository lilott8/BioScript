import colorlog
import networkx as nx

from compiler.data_structures.program import Program
from compiler.passes.analyses.call_graph import CallGraph
from compiler.passes.analyses.track_volume import VolumeTracker
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
        if len(self.program.functions) == 1:
            self.config.inline = False #if there are no other functions than the main, then there is nothing to inline
        if len(self.program.functions) >= 2 and self.config.inline is False:
            self.log.warning("Functions found and inlining flag is off. May experience varing results. Consider using the -inline flag at configuration")
        #Run inline before SSA
        if self.config.inline:
            In = Inline()
            self.program = In.transform(self.program)
        #Run SSA
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
            if key == 'loop_unroll' and not self.config.loopunroll:
                continue

            self.program = value.transform(self.program)

    def run_analysis(self):
        self.init_analysis()
        # TODO: This should be handled through decorator.
        for key, value in self.analysis.items():
            if key == 'volume_tracking' and not self.config.track_volume:
                continue
            self.program.analysis[key] = value.analyze(self.program)['result']

    def init_analysis(self):
        self.analysis['call_graph'] = CallGraph()
        self.analysis['def_use'] = DefUseChains()
        self.analysis['volume_tracking'] = VolumeTracker()
        # self.dependencies['analysis'].add_node('call_graph')

    def init_transforms(self):
        #if self.config.inline:
        #    self.transforms['inline'] = Inline()
        self.transforms['split_edges'] = SplitEdges()
        self.transforms['simd_expansion'] = SIMDExpansion()
        # self.dependencies['transforms'].add_node('split_edges')

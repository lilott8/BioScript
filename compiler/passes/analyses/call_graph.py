import networkx as nx

from compiler.data_structures.program import Program
from compiler.passes.analyses.bs_analysis import BSAnalysis


class CallGraph(BSAnalysis):

    def __init__(self):
        super().__init__("CallGraph")

    def analyze(self, program: Program) -> dict:
        graph = nx.DiGraph()
        for source, destinations in program.calls.items():
            graph.add_node(source)
            for destination in destinations:
                graph.add_node(destination)
                graph.add_cycle([source, destination])
        return {"name": self.name, "result": graph}

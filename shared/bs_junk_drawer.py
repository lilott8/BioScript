import colorlog
import networkx as nx


def write_graph(graph, name="dag.dot"):
    pos = nx.nx_agraph.graphviz_layout(graph)
    nx.draw(graph, pos=pos)
    nx.drawing.nx_pydot.write_dot(graph, name)

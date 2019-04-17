import colorlog
import networkx as nx


class Router(object):

    def __init__(self):
        self.log = colorlog.getLogger(self.__class__.__name__)
        pass

    def get_route(self, source, destination, graph: nx.DiGraph, algorithm: str = 'dijkstra'):
        self.log.info("We are ignoring algorithm for now.  Using Dijkstra's now.")
        return nx.algorithms.shortest_paths.shortest_path(graph, source, destination, algorithm)

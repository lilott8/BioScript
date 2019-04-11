import colorlog
import networkx as nx


class Scheduler(object):

    def __init__(self):
        self.log = colorlog.getLogger(self.__class__.__name__)
        pass

    def get_schedule(self, scheduler: str, dag: nx.DiGraph):
        self.log.debug("Ignoring scheduler for now.  Using topological sort.")
        return nx.algorithms.dag.topological_sort(dag)

import json
from enum import IntEnum

import networkx as nx


class WritableType(IntEnum):
    OTHER = 0
    GRAPH = 1
    JSON = 2


class Writable(object):

    def __init__(self, name: str, path: str, content, write_type: WritableType = WritableType.OTHER):
        self.name = name
        self.path = path
        self.content = content
        self.write_type = write_type

    def write(self):
        if self.write_type == WritableType.GRAPH:
            pos = nx.nx_agraph.graphviz_layout(self.content)
            nx.draw(self.content, pos=pos)
            nx.drawing.nx_pydot.write_dot(self.content, self.path)
            pass
        elif self.write_type == WritableType.JSON:
            with open(self.path, 'w') as out:
                out.write(json.dumps(self.content, sort_keys=True, indent=4))
            pass
        else:
            with open(self.path, 'w') as out:
                out.write(self.content)
            pass

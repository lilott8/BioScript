import json
import uuid
from collections import deque

import networkx as nx
from jsonschema import validate

from compiler.data_structures import Program
from compiler.targets.base_target import BaseTarget
from shared.components import NaiveAPI


class InkwellTarget(BaseTarget):

    def __init__(self, program: Program):
        super().__init__(program, "InkwellTarget")
        self.api = NaiveAPI()
        self.inputs = dict()
        self.components = dict()
        self.connections = dict()

    def build_dags(self):
        """
        This is a modified DAG construction algorithm.
        The primary difference is that all vertices
        have an output var and consume something.
        :return:
        """
        for root in self.program.functions:
            self.dags[root] = dict()
            # This maps an output variable (key) to a node in the graph.
            tags = set()
            for nid, block in self.program.functions[root]['blocks'].items():
                graph = nx.DiGraph()
                # Op nodes are defined as {output var, op}
                # Var nodes are defined as {var}
                for instruction in block.instructions:
                    if instruction.defs:
                        if instruction.defs.name not in tags:
                            tags.add(instruction.defs.name)
                            uses = list()
                            for use in instruction.uses:
                                uses.append(use.name)
                            graph.add_node(instruction.defs.name, iid=instruction.iid, op=instruction.op.name,
                                           defs=instruction.defs.name, uses=uses)
                        for uses in instruction.uses:
                            if not self.program.symbol_table.is_global(uses.name):
                                graph.add_edge(uses.name, instruction.defs.name)
                    else:
                        graph.add_node(instruction.iid, iid=instruction.iid,
                                       op=instruction.op.name, defs=None, uses=instruction.uses[0])
                        graph.add_edge(instruction.iid, instruction.uses[0])
                self.write_graph(graph)
                self.program.functions[root]['blocks'][nid].dag = graph
                self.dags[root][nid] = graph

    def transform(self, verify: bool = False):
        uid = uuid.uuid5(uuid.NAMESPACE_OID, self.program.name)
        output = {'name': self.program.name, 'layers': [{"id": str(uid), "name": "flow"}],
                  'components': [], 'connections': []}

        for root in self.program.functions:
            for bid, block in self.program.functions[root]['blocks'].items():
                queue = deque()
                seen = set()
                connections = set()
                # This gets all the nodes with no incoming edges
                # These are the source nodes of a graph.
                # This is an initialization step.
                for node in block.dag.nodes:
                    if len(block.dag.in_edges(node)) == 0:
                        queue.append(node)

                # A dictionary of the nodes and their associated data.
                graph = dict(block.dag.nodes('op'))

                # BFS!
                while queue:
                    current = queue.pop()
                    var = self.program.symbol_table.get_variable(current, root)
                    destination_op = graph[var.name]
                    if var.name not in self.components:
                        destination = self.build_component(var, uid, op=graph[var.name])
                        output['components'].append(destination)
                        self.components[var.name] = destination
                    else:
                        destination = self.components[var.name]

                    # All the edges that are coming into this
                    # node requires connections; build them.
                    # We should have seen *all* incoming edges,
                    # by now, which means we don't have to create.
                    for ancestor in block.dag.in_edges(var.name):
                        incoming = self.program.symbol_table.get_variable(ancestor[0], root)
                        # source_op = graph[incoming.name]
                        if incoming.name not in self.components:
                            source = self.build_component(incoming, uid, op=graph[incoming.name])
                            output['components'].append(source)
                            self.components[incoming.name] = source
                        else:
                            source = self.components[incoming.name]
                        connection_name = "{}_{}".format(incoming.name, var.name)
                        if connection_name not in connections:
                            output['connections'].append(
                                self.build_connection(source, destination, connection_name, uid))
                            connections.add(connection_name)

                    # Gather all the edges that leave this node and
                    # Add them to the queue if we haven't seen them.
                    for out in block.dag.out_edges(var.name):
                        if out not in seen:
                            queue.appendleft(out[1])
                    # We've now seen this
                    seen.add(current)
            self.verify_json(output, True)

    def verify_json(self, output: dict, verify: bool = False):
        if verify:
            self.log.info(json.dumps(output))
            with open('resources/parchmint_schema.json') as f:
                schema = json.load(f)
            validate(instance=output, schema=schema)
            self.log.debug("JSON validation successful")

    def build_component(self, var, layer: uuid, op: str = 'mix'):
        name = '{}_{}'.format(op, var.name)
        if var.is_global:
            out = self.api.get_component({'taxonomy': 'input', 'uuid': layer, 'name': name})
            self.inputs[var.name] = out
        else:
            out = self.api.get_component({'taxonomy': op, 'uuid': layer, 'name': name})
        self.components[name] = out
        self.connections[name] = set(n['label'] for n in out['ports'])
        return out

    def build_connection(self, source: dict, destination: dict, name: str, layer: uuid) -> dict:
        connection = dict()
        connection['id'] = str(uuid.uuid5(uuid.NAMESPACE_OID, '{}|{}'.format(source['name'], destination['name'])))
        connection['layer'] = str(layer)
        connection['name'] = name
        connection['sinks'] = list()
        label = None
        for p in source['ports']:
            if 'output' in p['label'] and p['label'] in self.connections[source['name']]:
                label = p['label']
                self.connections[source['name']].remove(label)
                break
        connection['source'] = {'component': source['id'], 'port': label}
        label = None
        for p in destination['ports']:
            if 'input' in p['label'] and p['label'] in self.connections[destination['name']]:
                label = p['label']
                self.connections[destination['name']].remove(label)
                break
        connection['sinks'].append({'component': destination['id'], 'port': label})

        return connection

    def write_mix(self) -> str:
        return "oh, you know!"

    def write_dispense(self) -> str:
        return "something"

    def write_split(self) -> str:
        pass

    def write_detect(self) -> str:
        pass

    def write_dispose(self) -> str:
        pass

    def write_expression(self) -> str:
        pass

    def write_branch(self) -> str:
        pass

import json
from collections import defaultdict

import networkx as nx
from jsonschema import exceptions
from jsonschema import validate

from compiler.data_structures import Program
from compiler.data_structures.ir import *
from compiler.data_structures.writable import Writable, WritableType
from compiler.targets.base_target import BaseTarget
from shared.components import FlowType
from shared.components import get_component_api


class InkwellTarget(BaseTarget):

    def __init__(self, program: Program):
        super().__init__(program, "InkwellTarget")
        self.api = get_component_api(self.config)
        self.inputs = dict()
        # All components required for executing this program.
        self.components = dict()
        # All the connections between components.
        self.connections = dict()
        # The DAG node to component entity mapping.
        self.node_to_component = dict()

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
            var_defs = defaultdict(lambda: list())
            var_uses = defaultdict(lambda: list())
            # This maintains the set of variables an instruction
            # defines or uses (basically a use/def chain)
            # Have we added the edge for this def yet?

            no_defs = {IRInstruction.NOP, IRInstruction.CONDITIONAL}
            for nid, block in self.program.functions[root]['blocks'].items():
                graph = nx.DiGraph()
                # Op nodes are defined as {output var, op}
                # Var nodes are defined as {var}
                for instruction in block.instructions:
                    if instruction.op not in no_defs:
                        # Add all the global variables to the instruction_uses.
                        if instruction.op == IRInstruction.DISPENSE and instruction.uses[0]['name'] not in graph:
                            graph.add_node(instruction.uses[0]['name'], defs=set(),
                                           uses={(instruction.uses[0]['name'], 1)}, op=instruction.op)
                        # Keep track of all the used variables,
                        # with offsets in an instruction
                        use = set()
                        # Keep track of all the defd variables,
                        # with offset in an instruction
                        deff = set()

                        if instruction.defs['offset'] >= 0:
                            name = f"{instruction.defs['name']}_{instruction.defs['offset']}"
                            if self.program.symbol_table.is_global(instruction.uses[0]['name']):
                                var_defs[name].append(instruction.uses[0]['name'])
                            else:
                                var_defs[name].append(instruction.iid)
                            deff.add((instruction.defs['name'], instruction.defs['offset']))
                        else:
                            if instruction.op == IRInstruction.SPLIT:
                                var = self.program.symbol_table.get_symbol(instruction.defs['name'], root)
                                offset = var.value.size
                            else:
                                offset = instruction.defs['offset']
                            for x in range(offset):
                                name = f"{instruction.defs['name']}_{x}"
                                var_defs[name].append(instruction.iid)
                                deff.add((instruction.defs['name'], x))

                        for uze in instruction.uses:
                            if uze['offset'] >= 0:
                                # This wraps all dispenses into one single node.
                                if self.program.symbol_table.is_global(uze['name']):
                                    name = uze['name']
                                else:
                                    name = f"{uze['name']}_{uze['offset']}"
                                var_uses[name].append(instruction.iid)
                                use.add((uze['name'], uze['offset']))
                            else:
                                # This if/else must be here because if the op is a split,
                                # and the op consumes the entire variable, then both
                                # the use['offset'] and def['offset'] are = 1.
                                if instruction.op == IRInstruction.SPLIT:
                                    var = self.program.symbol_table.get_symbol(uze['name'], root)
                                    offset = var.value.size
                                else:
                                    offset = instruction.defs['offset']
                                for x in range(offset):
                                    name = f"{uze['name']}_{x}"
                                    var_uses[name].append(instruction.iid)
                                    use.add((uze['name'], x))

                        for name, offset in use:
                            if self.program.symbol_table.is_global(name):
                                graph.nodes[name]['defs'].update(deff)
                            else:
                                graph.add_node(instruction.iid, op=instruction.op, defs=deff, uses=use)

                edges = set()
                for node in graph.nodes:
                    # Get the instruction in which this variable is defined.
                    # Source is the uses.
                    for source, src_offset in graph.nodes[node]['uses']:
                        # Destination is the defs.
                        if self.program.symbol_table.is_global(source):
                            siids = [source]
                        else:
                            siids = var_uses[f"{source}_{src_offset}"]
                        for destination, dst_offset in graph.nodes[node]['defs']:
                            # Build the edge from the source to the destination.
                            for sid in siids:
                                for did in var_uses[f"{destination}_{dst_offset}"]:
                                    if sid != did and (f"{sid}_{did}" not in edges and f"{did}_{sid}" not in edges):
                                        graph.add_edge(sid, did)
                                        edges.add(f"{sid}_{did}")

                if self.config.write_cfg:
                    self.program.write['cfg'] = Writable(self.program.name,
                                                         "{}/{}_{}_{}_dag.dot".format(self.config.output,
                                                                                      self.program.name, root, nid),
                                                         graph, WritableType.GRAPH)

                self.program.functions[root]['blocks'][nid].dag = graph
                self.dags[root][nid] = graph

    def transform(self, verify: bool = False):
        """
        Transform the IR into something Inkwell can understand.
        :param verify:
        :return:
        """
        # uid = uuid.uuid5(uuid.NAMESPACE_OID, self.program.name)
        output = {'name': self.program.name.replace('/', '_').replace('.', '_'),
                  'layers': [{"id": "flow", "name": "flow"}],
                  'components': [], 'connections': []}
        if self.program.config.flow_type == FlowType.ACTIVE:
            output['layers'].append({'id': 'control', 'name': 'control'})
        sequences = dict()
        component_set = dict()
        netlist = dict()
        for root in self.program.functions:
            sequences[root] = dict()
            for bid, block in self.program.functions[root]['blocks'].items():
                graph = block.dag
                sequences[root][bid] = {"on": {}, "off": {}}
                sinks = set()

                # Build the components.
                for node in graph.nodes:
                    if not graph.in_edges(node):
                        '''
                        This checks for dispense.  If there are no incoming edges,
                        then we know this must be a dispense port, so we build it.
                        '''
                        use = next(iter(graph.nodes[node]['uses']))
                        global_use = f"{use[0]}_{use[1]}"
                        if global_use not in self.components:
                            self.components[global_use] = self.build_component(global_use,
                                                                               output['layers'][0]['id'],
                                                                               graph.nodes[node]['op'],
                                                                               splits=use[1])
                            output['components'].append(self.components[global_use])
                        # This maps a disposals def to the correct global use.
                        # e.g.: a[2] = dispose aaa, a[0] and a[1] will map to
                        # the dispenser aaa.
                        for deff_name, deff_offset in graph.nodes[node]['defs']:
                            if f"{deff_name}_{deff_offset}" not in self.components:
                                self.components[f"{deff_name}_{deff_offset}"] = self.components[global_use]
                    elif not graph.out_edges(node):
                        '''
                        This checks for disposals.  If there are no outgoing edges,
                        then we know this must be a disposal port, so we build it,
                        and the corresponding connection right now.
                        '''
                        pass
                        use = next(iter(graph.nodes[node]['uses']))
                        component_name = f"{use[0]}_{use[1]}_disposal"
                        self.components[component_name] = self.build_component(
                            component_name, output['layers'][0]['id'], graph.nodes[node]['op'], splits=use[1]
                        )
                        output['components'].append(self.components[component_name])
                        connection_name = f"{use[0]}_{use[1]}->{component_name}"
                        if connection_name not in self.connections:
                            connection = self.build_connection(
                            self.components[f'{use[0]}_{use[1]}'], self.components[component_name],
                                connection_name, output['layers'][0]['id'],
                            self.program.symbol_table.is_global(use[1])
                            )
                            self.connections[connection_name] = connection
                            output['connections'].append(connection)
                    else:
                        '''
                        Iterate all the other nodes that exist.
                        '''
                        deff_name = '__'.join("%s_%s" % tup for tup in graph.nodes[node]['defs'])
                        self.components[deff_name] = self.build_component(deff_name, output['layers'][0]['id'],
                                                                          graph.nodes[node]['op'],
                                                                          splits=len(graph.nodes[node]['defs']))
                        output['components'].append((self.components[deff_name]))
                        for name, offset in graph.nodes[node]['defs']:
                            # Access an item in a set but don't iterate.
                            # Disposals will have only one use, thus we can
                            # safely check the first element if it's not global,
                            # it doesn't matter what anything else is.
                            component_name = f"{name}_{offset}"
                            if component_name not in self.components:
                                self.components[component_name] = self.components[deff_name]

                # Build the connections between those components.
                for node in block.dag.nodes:
                    for name, offset in graph.nodes[node]['uses']:
                        use_name, use_offset = next(iter(graph.nodes[node]['uses']))
                        if self.program.symbol_table.is_global(use_name):
                            source = self.components[f"{use_name}_{use_offset}"]
                        else:
                            source = self.components[f"{name}_{offset}"]
                        for deff_name, deff_offset in graph.nodes[node]['defs']:
                            deff_var = self.program.symbol_table.get_symbol(deff_name)
                            destination = self.components[f"{deff_name}_{deff_offset}"]
                            connection_name = f"{source['name']}->{destination['name']}"
                            if source['name'] != destination['name'] and connection_name not in self.connections:
                                self.connections[connection_name] = self.build_connection(
                                    source, destination, connection_name,
                                    output['layers'][0]['id'], deff_var.value.is_global)
                                output['connections'].append(self.connections[connection_name])

                for component in output['components']:
                    if component['entity'] == 'Input-port':
                        component['name'] = f"dispense_{component['name']}"

                if self.config.flow_type == FlowType.ACTIVE:
                    activations = self.generate_activations(output, component_set, block.dag, sinks)
                    sequences[root][bid]['timing'] = activations

            verified = self.verify_json(output, True)
            if verified:
                netlist[root] = output
            """
            The check happens here because this is a shared function.
            It has no access to the config object.
            """
            if verified and self.config.write_out and self.config.write_cfg:
                json_dag_name = "{}_{}_dag_from_json".format(self.program.name, root)
                self.program.write["json_graph"] = Writable(json_dag_name,
                                                            "{}/{}.dot".format(self.config.output, json_dag_name),
                                                            self.json_to_graph(output, root), WritableType.GRAPH)
                # self.json_to_graph(output, root)
        if self.config.flow_type == FlowType.ACTIVE:
            self.program.write['activations'] = Writable("{}_activations".format(self.program.name),
                                                         "{}/{}_activations.json".format(self.config.output,
                                                                                         self.program.name),
                                                         sequences, WritableType.JSON)
        for root in netlist:
            netlist_name = "{}_netlist_{}".format(self.program.name, root)
            self.program.write['{}_netlist_{}'] = Writable(netlist_name,
                                                           "{}/{}.json".format(self.config.output, netlist_name),
                                                           netlist[root], WritableType.JSON)

    def json_to_graph(self, spec, function_name):
        graph = nx.DiGraph()
        for component in spec['components']:
            graph.add_node(component['id'], label=component['entity'])
        for connection in spec['connections']:
            for sink in connection['sinks']:
                if 'source' in connection:
                    graph.add_edge(connection['source']['component'], sink['component'], label=connection['name'])
        return graph

    def verify_json(self, output: dict, verify: bool = False) -> bool:
        if verify:
            try:
                with open(self.program.config.schema) as f:
                    schema = json.load(f)
                validate(instance=output, schema=schema)
                self.log.debug("JSON validation successful")
                return True
            except exceptions.ValidationError as e:
                self.log.warning(str(e))
                return False

    def generate_activations(self, components: dict, component_set, dag, sinks) -> list:
        """
        :param components: inkwell json.
        :param component_set: Set of components available for selection.
        :param dag: multidigraph.MultiDiGraph.
        :param sinks:
        :return: List of timesteps and their activations.
        """

        def find_start(e, dispense_dict, mix_defs_dict):
            if e in dispense_dict:
                return dispense_dict[e]
            else:
                return mix_defs_dict[e]

        def find_end(sinks, paths):
            for s in sinks:
                if s in paths:
                    return s

        complete = set(range(1, len(dag.nodes)))
        mapping_names_to_graph = {}
        mapping_graph_to_names = {}
        print(dag.nodes, dag.edges)
        for i, data in dag.nodes('data'):
            op = data['op']
            if op == 'DISPOSE':
                mapping_names_to_graph[data['defs']] = i
                mapping_graph_to_names[i] = data['defs']
            elif op == 'MIX':
                mapping_names_to_graph[data['defs']] = i
                mapping_graph_to_names[i] = data['defs']
            elif op == 'SPLIT':
                pass
            elif op == 'HEAT':
                pass
            elif op == 'DISPENSE':
                key = None
                for s in data['uses']:
                    key = s
                    break
                mapping_graph_to_names[i] = key
                mapping_names_to_graph[key] = i
            else:
                print('hello', data)
                pass
        print('hey')
        print(dag.nodes, dag.edges)
        sink_names = set(map(lambda s: s[7:], sinks))
        sink_nums = set(map(lambda s: mapping_names_to_graph[s], sink_names))
        timing = list()
        paths = {}

        # where start originates from...
        dispense_dict = {}
        mix_defs_dict = {}

        for block in self.program.functions['main']['blocks'].values():
            for instr in block.instructions:
                if type(instr) == Dispose:
                    t = {}
                    name = instr.uses[0].name
                    assert (name in mapping_names_to_graph)
                    node_num = mapping_names_to_graph[name]
                    for path in paths.values():
                        for pp in path.values():
                            if node_num in pp:
                                t['on'] = pp
                                t['off'] = complete - pp
                                break
                    assert (len(t['on']) != 0)
                    timing.append(t)
                elif type(instr) == Mix:
                    # schedule the 1st element to be mixed.
                    e = instr.uses[0].name
                    start = find_start(e, dispense_dict, mix_defs_dict)
                    end = find_end(sink_nums, paths[start])
                    t1 = {'on': paths[start][end], 'off': (complete - paths[start][end])}

                    # schedule closing of valves
                    t2 = {'on': set(), 'off': complete}

                    # schedule the 2nd element to be mixed.
                    e = instr.uses[1].name
                    start = find_start(e, dispense_dict, mix_defs_dict)
                    t3 = {'on': paths[start][end], 'off': (complete - paths[start][end])}

                    # append timings
                    timing.append(t1)
                    timing.append(t2)
                    timing.append(t3)

                    # picked an arbitary start node
                    mix_defs_dict[instr.defs.name] = start
                elif type(instr) == Split:
                    pass
                elif type(instr) == Heat:
                    pass
                elif type(instr) == Detect:
                    pass
                elif type(instr) == Dispense:
                    node_name = instr.uses[0].name
                    dispense_dict[instr.defs.name] = node_name
                    start = mapping_names_to_graph[node_name]
                    paths[node_name] = {}
                    for n, path in nx.single_source_shortest_path(dag, start).items():
                        if n not in sink_nums:
                            continue
                        paths[node_name][n] = set(path)
                else:
                    self.log.warning('Unhandled instruction')

        self.log.info("Generating activation sequences")
        for i, t in enumerate(timing):
            t['on'] = set(map(lambda x: mapping_graph_to_names[x], t['on']))
            t['on'] = list(t['on'])
            t['off'] = set(map(lambda x: mapping_graph_to_names[x], t['off']))
            t['off'] = list(t['off'])
            # self.log.info('t{}:   {}'.format(i, t))
        return timing

    def build_schedule(self, dag: nx.DiGraph, with_dispense: bool = False):
        schedule = list(nx.algorithms.dag.topological_sort(dag))
        graph = dict(dag.nodes("data"))
        # Filter out the dispenses if necessary.
        if not with_dispense:
            temp = list()
            for node in schedule:
                if not graph[node]['op'].lower() == 'dispense':
                    temp.append(node)
            schedule = temp
        return schedule

    def build_component(self, name, layer: str, op: IRInstruction = IRInstruction.MIX, splits: int = 1):
        """
        This builds the attributes required for defining
        a component on a continuous flow device.
        :param name: Unique identifier of the component to be found,
            note: this is a composite of function name, basic block name,
            op name, and emitting variable name.
        :param layer: Which layer does this operation occur on.
        :param op: What is the operation.
        :param splits: If it's a split, how many?
        :return: The created component.
        """
        if op.name == 'DISPENSE':
            out = self.api.build_component({'taxonomy': 'input', 'uuid': layer, 'name': name, 'splits': splits,
                                            'flow': self.program.config.flow_type})
            self.inputs[name] = out
        else:
            out = self.api.build_component({'taxonomy': op.name, 'uuid': layer, 'name': name, 'splits': splits,
                                            'flow': self.program.config.flow_type})
        # Each port must have it's own connections, so we list all the ports here.
        self.connections[name] = set(n['label'] for n in out['ports'])
        return out

    def build_connection(self, source: dict, destination: dict, name: str, layer: str,
                         source_global: bool = False) -> dict:
        """
        Builds a connection between two components.
        :param source: Source component ID.
        :param destination: Destination component ID.
        :param name: Name of connection.
        :param layer: What layer does this belong on?
        :param source_global: Is the source a global variable?
        :return: A dictionary forming the connection.
        """
        connection = dict()
        connection['id'] = f"{source['name']}|{destination['name']}"
        connection['layer'] = layer
        connection['name'] = name
        connection['sinks'] = list()
        label = None
        for p in source['ports']:
            if 'output' in p['label'] and p['label'] in self.connections[source['name']]:
                label = p['label']
                if not source_global:
                    self.connections[source['name']].remove(label)
                break
        connection['source'] = {'component': source['id'], 'port': label if label is not None else "none"}
        label = None
        for p in destination['ports']:
            if 'input' in p['label'] and p['label'] in self.connections[destination['name']]:
                label = p['label']
                self.connections[destination['name']].remove(label)
                break
        connection['sinks'].append({'component': destination['id'], 'port': label if label is not None else "none"})

        return connection

    def get_machine_code(self):
        return {}

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

import json
import uuid

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

    def transform(self, verify: bool = False):
        uid = uuid.uuid5(uuid.NAMESPACE_OID, self.program.name)
        output = {'name': self.program.name, 'layers': [{"id": str(uid), "name": "flow"}],
                  'components': [], 'connections': []}

        for root in self.program.functions:
            for bid, block in self.program.functions[root]['blocks'].items():
                for node, attr in list(block.dag.nodes(data=True)):
                    if 'op' in attr:
                        var = self.program.symbol_table.get_local(node, root)
                        component_name = '{}_{}'.format(attr['op'], var.name)
                        if component_name not in self.components:
                            # build the component
                            component = self.build_component(var, uid, op=attr['op'])
                            output['components'].append(component)
                        else:
                            component = self.components[component_name]

                        graph = dict(block.dag.nodes('op'))
                        for source, destination in block.dag.out_edges(node):
                            op = graph[destination]
                            if op:
                                dest_var = self.program.symbol_table.get_local(destination, root)
                                dest_component_name = '{}_{}'.format(op, dest_var.name)
                                if dest_component_name not in component:
                                    dest_component = self.build_component(dest_var, uid, op)
                                    output['components'].append(dest_component)
                                else:
                                    dest_component = self.components[dest_component_name]
                                # It shouldn't matter how you try to reference a connection.
                                connection_a = '{}|{}'.format(component_name, dest_component_name)
                                connection_b = '{}|{}'.format(dest_component_name, component_name)
                                # Build the connection.
                                connection = self.build_connection(component, dest_component, connection_a, uid)
                                output['connections'].append(connection)
        verify = True
        if verify:
            self.log.info(json.dumps(output))
            with open('resources/parchmint_schema.json') as f:
                schema = json.load(f)
            validate(instance=output, schema=schema)
            self.log.debug("JSON validation successful")

        return False

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
        if name.lower() == 'mix_g0|detect_x0':
            x = 1
        connection = dict()
        connection['id'] = str(uuid.uuid5(uuid.NAMESPACE_OID, '{}|{}'.format(source['name'], destination['name'])))
        connection['layer'] = str(layer)
        connection['name'] = name
        connection['sinks'] = list()
        self.log.critical("Ports are hard coded as index 0.")
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

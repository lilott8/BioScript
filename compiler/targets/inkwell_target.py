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

    def transform(self, verify: bool = False):
        uid = uuid.uuid5(uuid.NAMESPACE_OID, self.program.name)
        output = {'name': self.program.name, 'layers': [{"id": str(uid), "name": "flow"}],
                  'components': [], 'connections': []}

        inputs = dict()
        outputs = dict()
        # Mapping of components already
        # added to the parchmint file.
        components = dict()

        # for i in self.program.globals:
        #     component = self.api.get_component({'taxonomy': 'input', 'name': i, 'uuid': uuid})
        #     inputs[i] = component
        #     components[i] = component
        #     output['components'].append(component)

        for root in self.program.functions:
            for bid, block in self.program.functions[root]['blocks'].items():
                for node, attr in list(block.dag.nodes(data=True)):
                    if 'op' in attr:
                        var = self.program.symbol_table.get_local(node, root)
                        if var.is_global:
                            components[var.name] = self.api.get_component(
                                {'taxonomy': 'input', 'uuid': uid, 'name': '{}_{}'.format(attr['op'], var.name)})
                            output['components'].append(components[var.name])
                        self.log.info(node)
                        self.log.info(var)
                        pass
                break
        #             """
        #             We have 2 cases:
        #             1) We have an operation (component)
        #                 that needs to be added to the device.
        #             2) We have to build the connection
        #                 between two components.
        #             """
        #             if op is not None:
        #                 if var not in components:
        #                     components[var] = self.api.get_component(
        #                         {'taxonomy': op, 'uuid': uid, 'name': '{}_{}'.format(var, op)})
        #                     output['components'].append(components[var])
        #             else:
        #                 self.log.info("{}: in: {}\t out: {}".format(var, block.dag.in_edges(var), block.dag.out_edges(var)))
        #                 sinks = {b for a, b in block.dag.out_edges(var)}
        #                 sinks.discard(var)
        #                 sources = {a for a, b in block.dag.in_edges(var)}
        #                 sources.discard(var)
        #                 output['connections'].append({
        #                     'id': '',
        #                     'layer': str(uid),
        #                     'name': '{}_{}'.format(1, 2),
        #                     'sinks': [
        #                         {
        #                             'component': '',
        #                             'port': ''
        #                          }
        #                     ],
        #                     'source':
        #                         {
        #                             'component': '',
        #                             'port': ''
        #                         }
        #                 }
        #                 )
        #                 # self.log.info("{}, {}".format(var, op))
        #                 # self.log.info('build the connection')
        # # self.log.info(json.dumps(output))

        verify = False
        if verify:
            with open('resources/parchmint_schema.json') as f:
                schema = json.load(f)
            validate(instance=output, schema=schema)
            self.log.debug("JSON validation successful")

        return False

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

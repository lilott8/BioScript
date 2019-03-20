import json
import uuid
from collections import deque

from jsonschema import validate

from compiler.data_structures import Program
from compiler.targets.base_target import BaseTarget


class InkwellTarget(BaseTarget):

    def __init__(self, program: Program):
        super().__init__(program, "InkwellTarget")

    def transform(self, verify: bool = False):
        uid = uuid.uuid5(uuid.NAMESPACE_OID, self.program.name)
        output = {'name': self.program.name, 'layers': [{"id": str(uid), "name": "flow"}],
                  'components': [], 'connections': []}

        for inputs in self.program.globals:
            self.log.info(inputs)
            # TODO: abstract this. This should be received from the component generation call. Which means this should be stubbed.
            component = {
                'entity': 'Input',
                'id': inputs + "_id",
                "layers": [str(uid)],
                "name": inputs,
                "ports": [
                    {
                        "label": "",
                        "layer": str(uid),
                        "x": 10,
                        "y": 20
                    }
                ],
                "x-span": 20,
                "y-span": 20
            }
            output['components'].append(component)

        queue = deque()
        queue.append(self.program.functions['main']['entry'])
        while queue:
            block = queue.popleft()
            self.log.info("Exploring block: " + str(block))
            for node, edge in self.program.bb_graph.out_edges(block):
                queue.append(edge)
            for instruction in self.program.functions['main']['blocks'][block].instructions:
                self.log.debug(instruction.write(self))

        verify = True
        if verify:
            with open('resources/parchmint_schema.json') as f:
                schema = json.load(f)
            validate(instance=output, schema=schema)
            self.log.debug("JSON validation successful")

        return False

    def write_mix(self, ir) -> str:
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

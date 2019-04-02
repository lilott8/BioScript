import abc

import colorlog


class ComponentAPI(object, metaclass=abc.ABCMeta):

    def __init__(self):
        self.log = colorlog.getLogger()

    @abc.abstractmethod
    def get_component(self, attr: dict):
        pass


class NetworkAPI(ComponentAPI):

    def __init__(self):
        super().__init__()

    def get_component(self, attr: dict):
        pass


class NaiveAPI(ComponentAPI):
    def __init__(self):
        super().__init__()

    def get_component(self, attr: dict):
        component = dict()
        if attr['taxonomy'].lower() == 'input' or attr['taxonomy'].lower() == 'dispense':
            component['entity'] = 'IO-port'
            component['id'] = attr['name'] + "_id"
            component["layers"] = [str(attr['uuid'])]
            component["name"] = attr['name']
            component["ports"] = [
                {
                    "label": "output1",
                    "layer": str(attr['uuid']),
                    "x": 70,
                    "y": 140
                },
                {
                    "label": "output2",
                    "layer": str(attr['uuid']),
                    "x": 140,
                    "y": 70
                },
                {
                    "label": "output3",
                    "layer": str(attr['uuid']),
                    "x": 70,
                    "y": 0
                },
                {
                    "label": "output4",
                    "layer": str(attr['uuid']),
                    "x": 70,
                    "y": 70
                }
            ]
            component["x-span"] = 140
            component["y-span"] = 140
        elif attr['taxonomy'].lower() == 'mix':
            component['entity'] = 'serpentine-mixer'
            component['id'] = attr['name'] + "_id"
            component['layers'] = [str(attr['uuid'])]
            component['name'] = attr['name']
            component['ports'] = [
                {
                    'label': 'input1',
                    'layer': str(attr['uuid']),
                    'x': 0,
                    'y': 52
                },
                {
                    'label': 'input2',
                    'layer': str(attr['uuid']),
                    'x': 0,
                    'y': 8
                },
                {
                    'label': 'output',
                    'layer': str(attr['uuid']),
                    'x': 150,
                    'y': 30
                }
            ]
            component['x-span'] = 150
            component['y-span'] = 60
        elif attr['taxonomy'].lower() == 'detect':
            component['entity'] = 'Detect'
            component['id'] = attr['name'] + "_id"
            component['layers'] = [str(attr['uuid'])]
            component['name'] = attr['name']
            component['ports'] = [
                {
                    'label': 'input1',
                    'layer': str(attr['uuid']),
                    'x': 10,
                    'y': 0
                },
                {
                    'label': 'output',
                    'layer': str(attr['uuid']),
                    'x': 10,
                    'y': 20
                }
            ]
            component['x-span'] = 20
            component['y-span'] = 20
        elif attr['taxonomy'].lower() == 'dispose':
            component['entity'] = 'IO-port'
            component['id'] = attr['name'] + "_id"
            component['layers'] = [str(attr['uuid'])]
            component['name'] = attr['name']
            component["ports"] = [
                {
                    "label": "input1",
                    "layer": str(attr['uuid']),
                    "x": 70,
                    "y": 140
                },
                {
                    "label": "input2",
                    "layer": str(attr['uuid']),
                    "x": 140,
                    "y": 70
                },
                {
                    "label": "input3",
                    "layer": str(attr['uuid']),
                    "x": 70,
                    "y": 0
                },
                {
                    "label": "input4",
                    "layer": str(attr['uuid']),
                    "x": 70,
                    "y": 70
                }
            ]
            component["x-span"] = 140
            component["y-span"] = 140
        elif attr['taxonomy'].lower() == 'split':
            component['entity'] = 'Split'
            component['id'] = attr['name'] + "_id"
            component['layers'] = [str(attr['uuid'])]
            component['name'] = attr['name']
            component['x-span'] = 20
            component['y-span'] = 20
            ports = list()
            component['ports'] = [
                {
                    "label": 'input1',
                    'layer': str(attr['uuid']),
                    'x': 10,
                    'y': 0
                }
            ]
            for x in range(0, attr['splits']):
                component['ports'].append(
                    {
                        'label': 'output{}'.format(x + 1),
                        'layer': str(attr['uuid']),
                        'x': component['x-span'] / (x + 1),
                        'y': 20
                    }
                )

        elif attr['taxonomy'].lower() == 'heat':
            component['entity'] = 'Heater'
            component['id'] = attr['name'] + "_id"
            component['layers'] = [str(attr['uuid'])]
            component['name'] = attr['name']
            component['ports'] = [
                {
                    'label': 'input1',
                    'layer': str(attr['uuid']),
                    'x': 10,
                    'y': 0
                },
                {
                    'label': 'output',
                    'layer': str(attr['uuid']),
                    'x': 10,
                    'y': 20
                }
            ]
            component['x-span'] = 20
            component['y-span'] = 20
        else:
            self.log.error("No taxonomy for: {}".format(attr['taxonomy']))

        return component

    def build_connection(self, a: dict, b: dict) -> dict:
        pass

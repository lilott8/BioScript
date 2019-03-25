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
            component['entity'] = 'Input'
            component['id'] = attr['name'] + "_id"
            component["layers"] = [str(attr['uuid'])]
            component["name"] = attr['name']
            component["ports"] = [
                {
                    "label": "",
                    "layer": str(attr['uuid']),
                    "x": 10,
                    "y": 20
                }
            ]
            component["x-span"] = 20
            component["y-span"] = 20
        elif attr['taxonomy'].lower() == 'mix':
            component['entity'] = 'Mixer'
            component['id'] = attr['name'] + "_id"
            component['layers'] = [str(attr['uuid'])]
            component['name'] = attr['name']
            component['ports'] = [
                {
                    'label': 'input1',
                    'layer': str(attr['uuid']),
                    'x': 5,
                    'y': 0
                },
                {
                    'label': 'input2',
                    'layer': str(attr['uuid']),
                    'x': 15,
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
        else:
            self.log.error("No taxonomy for: {}".format(attr['taxonomy']))

        return component

    def build_connection(self, a: dict, b: dict) -> dict:
        pass

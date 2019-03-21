import abc


class ComponentAPI(object, metaclass=abc.ABCMeta):

    def __init__(self):
        pass

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
        if attr['taxonomy'].lower() == 'input':
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
            component['layers'] = [attr[str(attr['uuid'])]]
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

        return component

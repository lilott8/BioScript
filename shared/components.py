import abc
import copy
import json
from enum import IntEnum

import colorlog


class FlowType(IntEnum):
    ACTIVE = 0
    PASSIVE = 1


def get_component_api(config):
    if config.use_local_db:
        return NaiveAPI(config)
    else:
        return NetworkAPI(config)


class ComponentAPI(object, metaclass=abc.ABCMeta):

    def __init__(self, config):
        self.log = colorlog.getLogger(self.__class__.__name__)
        self.config = config
        self.filter = config.flow_type

    @abc.abstractmethod
    def build_component(self, attr: dict):
        pass

    @abc.abstractmethod
    def get_component(self, op: str):
        pass


class NetworkAPI(ComponentAPI):

    def __init__(self, config):
        super().__init__(config)
        # self.connection = connection

    def build_component(self, attr: dict):
        pass

    def get_component(self, op: str):
        pass


class NaiveAPI(ComponentAPI):
    def __init__(self, config):
        super().__init__(config)
        self.components = dict()
        with open(config.library, 'r') as f:
            library = json.loads(f.read())
        for key in library:
            self.components[key] = library[key][self.filter.name.lower()][0]

    def get_mix(self):

        pass

    def get_split(self):
        pass

    def get_heat(self):
        pass

    def get_detect(self):
        pass

    def get_io(self):
        pass

    def get_component(self, op: str):
        op = op.lower()
        if op not in self.components:
            raise Exception("No component: {} has been defined.".format(op))

        return self.components[op]

    def build_component(self, attr: dict):
        taxonomy = attr['taxonomy'].lower()
        if taxonomy == 'dispose':
            taxonomy = 'output'
        component = copy.deepcopy(self.components[taxonomy])
        component['name'] = attr['name']
        component['id'] = attr['name'] + "_id"
        for port in component['ports']:
            if attr['flow'] == FlowType.PASSIVE:
                port['layer'] = attr['uuid']
            else:
                self.log.fatal(
                    "You didn't implement the active flow portion.  You need to append to the appropriate layers.")
        return component

    def build_connection(self, a: dict, b: dict) -> dict:
        pass

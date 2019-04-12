import json

import colorlog
import networkx as nx

from flow_synth.algorithms.router import Router
from flow_synth.algorithms.scheduler import Scheduler
from flow_synth.config.config import Config


class FlowSynthesizer(object):

    def __init__(self, config: Config):
        self.log = colorlog.getLogger(self.__class__.__name__)
        self.config = config
        self.dag = nx.drawing.nx_pydot.read_dot(self.config.dag_path)

    def synthesize(self):
        schedule = Scheduler().get_schedule(self.config.scheduler, self.dag)
        router = Router()
        with open(self.config.input, 'r') as f:
            json_chip = json.load(f)
        chip = self.build_chip(json_chip)
        activations = self.build_activations(chip, schedule, Router())
        self.log.info(chip)
        self.log.info(activations)
        self.log.info('You are synthesizing a flow chip')

    def build_chip(self, layout: dict) -> dict:
        chip = dict()
        for layer in layout['layers']:
            chip[layer['id']] = nx.DiGraph(name=layer['name'])
        for component in layout['components']:
            for layer in component['layers']:
                chip[layer].add_node(component['id'], entity=component['entity'], name=component['name'])
        for connection in layout['connections']:
            for sink in connection['sinks']:
                chip[connection['layer']].add_edge(connection['source'], sink)
        return chip

    def build_activations(self, chip: dict, schedule, router: Router = Router()) -> list:
        activations = list()
        self.log.info(schedule)
        

        return activations

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

    def synthesize(self):
        scheduler = Scheduler()
        router = Router()
        with open(self.config.input, 'r') as f:
            json_chip = json.load(f)
        chip = self.build_chip(json_chip)
        self.log.info(json_chip)
        self.log.info('You are synthesizing a flow chip')

    def build_chip(self, layout: dict) -> nx.DiGraph:
        self.log.debug("Start here!")
        return None

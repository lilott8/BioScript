import colorlog

from flow_synth.config.config import Config


class FlowSynthesizer(object):

    def __init__(self, config: Config):
        self.log = colorlog.getLogger(self.__class__.__name__)
        self.config = config

    def synthesize(self):
        self.log.info('You are synthesizing a flow chip')

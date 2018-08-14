import colorlog

from config.config import Config


class Problem(object):

    def __init__(self):
        self.log = colorlog.getLogger(self.__class__.__name__)
        self.config = Config.getInstance(None)

    def run(self):
        raise Exception("Unimplemented Function.")

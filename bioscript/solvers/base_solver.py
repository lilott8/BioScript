import colorlog

from config.config import Config


class BaseSolver(object):

    def __init__(self):
        self.log = colorlog.getLogger(self.__class__.__name__)
        self.config = Config.getInstance(None)

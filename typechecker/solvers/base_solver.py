import sys

print('TYPE_CHECKER: ', sys.path)


import logging
from config.config import Config


class BaseSolver(object):

    def __init__(self):
        self.log = logging.getLogger(self.__class__.__name__)
        self.config = Config.getInstance(None)

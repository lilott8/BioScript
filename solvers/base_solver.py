import colorlog

import config


class BaseSolver(object):

    def __init__(self):
        self.log = colorlog.getLogger(self.__class__.__name__)
        self.config = config.Config.get_instance(None)

    def solve(self, problem) -> bool:
        raise NotImplementedError

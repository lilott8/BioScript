import colorlog


class BaseSolver(object):

    def __init__(self, config):
        self.log = colorlog.getLogger(self.__class__.__name__)
        self.config = config

    def solve(self, problem) -> bool:
        raise NotImplementedError

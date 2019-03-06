import colorlog


class BaseSolver(object):

    def __init__(self):
        self.log = colorlog.getLogger(self.__class__.__name__)

    def solve(self, problem) -> bool:
        raise NotImplementedError

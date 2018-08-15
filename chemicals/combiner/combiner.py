import colorlog


class Combiner(object):

    def __init__(self):
        self.log = colorlog.getLogger(__name__)

    def combine(self, *args: list) -> set:
        """
        Takes a list of sets and returns a union of them.
        :param args: List of sets containing ChemTypes types.
        :return: Set of union-ed ChemTypes types.
        """
        raise NotImplementedError

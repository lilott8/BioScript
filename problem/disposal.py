from .problem import Problem


class Disposal(Problem):

    def __init__(self):
        Problem.__init__(self)
        self.log.info("Disposal problem.")

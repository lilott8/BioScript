from .problem import Problem


class Storage(Problem):

    def __init__(self):
        Problem.__init__(self)
        self.log.info("Storage problem.")

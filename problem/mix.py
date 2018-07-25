from .problem import Problem


class Mix(Problem):

    def __init__(self):
        Problem.__init__(self)
        self.log.info("Mix problem.")

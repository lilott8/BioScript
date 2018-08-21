from .base_solver import BaseSolver


class NaiveSolver(BaseSolver):

    def __init__(self):
        super().__init__()

    def solve(self, problem) -> bool:
        self.log.info(problem)
        return True

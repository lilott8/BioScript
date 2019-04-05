
from compiler.targets.base_target import BaseTarget


class PuddleTarget(BaseTarget):

    def __init__(self, program, inline=False):
        super().__init__(program, "PuddleTarget", inline)

    def transform(self):
        return False

    def write_mix(self) -> str:
        pass

    def write_split(self) -> str:
        pass

    def write_detect(self) -> str:
        pass

    def write_dispose(self) -> str:
        pass

    def write_dispense(self) -> str:
        pass

    def write_expression(self) -> str:
        pass

    def write_branch(self) -> str:
        pass

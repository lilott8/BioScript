from compiler.targets.base_target import BaseTarget


class MFSimTarget(BaseTarget):

    def __init__(self, program):
        super().__init__(program, "MFSimTarget")

    def transform(self):
        return False

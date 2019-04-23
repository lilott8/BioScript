from compiler.targets.base_target import BaseTarget


class MFSimTarget(BaseTarget):

    def __init__(self, config, program):
        super().__init__(config, program, "MFSimTarget")

    def transform(self):
        return False

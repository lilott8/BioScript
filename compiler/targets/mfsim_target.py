from compiler.targets.base_target import BaseTarget


class MFSimTarget(BaseTarget):

    def __init__(self, program, inline=False):
        super().__init__(program, "MFSimTarget", inline)

    def transform(self):
        return False

import colorlog

from compiler.passes.bs_pass import BSPass


class BSTransform(metaclass=BSPass):

    def __init__(self, pass_name: str):
        self.log = colorlog.getLogger(self.__class__.__name__)
        self.name = pass_name

    @BSPass.transform
    def transform(self):
        pass

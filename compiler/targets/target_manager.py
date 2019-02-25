import colorlog

import config.config


class TargetManager(object):

    def __init__(self, symbol_table, ir):
        self.config = config.Config.getInstance(None)
        self.log = colorlog.getLogger(self.__class__.__name__)
        self.log.debug("Initializing target manager.")
        self.ir = ir
        self.symbol_table = symbol_table

    def transform(self):
        target = self.config.target.get_target(self.symbol_table, self.ir)
        self.log.info("Visiting: {}".format(target.name))

        if self.config.debug:
            # target.print_program()
            pass

import os
import sys

import colorlog


class Config(object):

    def __init__(self, args):
        self.log = colorlog.getLogger(self.__class__.__name__)
        """
        General Stuff
        """
        self.debug = args.debug
        self.input = args.input
        self.input_file = args.input.split("/")[-1].split(".")[0]
        self.path = os.path.dirname(sys.modules['__main__'].__file__)
        self.output = args.output
        self.scheduler = self.get_scheduler(args.scheduler)
        self.router = args.router

    def get_scheduler(self, schedule: str) -> str:
        if schedule == 'list':
            pass
        elif schedule == 'path':
            pass
        elif schedule == 'priority':
            pass
        elif schedule == 'evo':
            pass
        elif schedule == 'ilp':
            pass
        return ""

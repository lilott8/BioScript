import abc
import argparse

import colorlog


class BaseCLI(metaclass=abc.ABCMeta):

    def __init__(self, args):
        self.log = colorlog.getLogger(self.__class__.__name__)
        self.args = args
        self.parser = argparse.ArgumentParser()
        """
        Generic Parser Arguments
        """
        self.parser.add_argument('-i', '--input', help='input file.', required=True)
        self.parser.add_argument('-d', '--debug', help='Enable debug mode.', action='store_true', default=False)
        self.parser.add_argument('-wd', '--working-directory', help="Working path.", default="./", type=str)
        self.parser.add_argument('-o', '--output', help='Directory to output files to.', type=str, default=False)

    @abc.abstractmethod
    def validate_config(self):
        pass

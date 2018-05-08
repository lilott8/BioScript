import logging
import sys
import argparse
from config.config import Config
from config.cli import Cli


def main(args):
    cli = Cli(args)
    logging.warning("Hello, world")



if __name__ == '__main__':
    logging.basicConfig(level=logging.DEBUG)
    main(sys.argv[1:])

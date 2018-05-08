import logging
import sys
from config.cli import Cli
from config.config import Config
from enums.problem import Problem


def main(args):
    cli = Cli(args)
    logging.warning("Hello, world")
    config = Config.getInstance(None)

    if config.problem == Problem.MIX:
        logging.info("Running a mix operation")
    elif config.problem == Problem.DISPOSAL:
        logging.info("Running a disposal operation")
    else:
        logging.info("Running a storage operation")


if __name__ == '__main__':
    logging.basicConfig(level=logging.DEBUG)
    main(sys.argv[1:])

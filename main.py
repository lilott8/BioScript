import logging
import sys
from config.cli import Cli
from config.config import Config
from enums.problem import Problem
from problem.mix import Mix
from problem.storage import Storage
from problem.disposal import Disposal


def main(args):
    cli = Cli(args)
    logging.warning("Hello, world")
    config = Config.getInstance(None)

    if config.problem == Problem.MIX:
        logging.info("Running a mix problem")
        mix = Mix()
    elif config.problem == Problem.DISPOSAL:
        logging.info("Running a disposal problem")
        dispose = Disposal()
    else:
        logging.info("Running a storage problem")
        store = Storage()


if __name__ == '__main__':
    logging.basicConfig(level=logging.DEBUG)
    main(sys.argv[1:])

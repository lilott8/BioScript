import logging
import sys

import colorlog

from config.cli import Cli
from config.config import Config
from problem.bioscript import BioScript
from problem.disposal import Disposal
from problem.mix import Mix
from problem.storage import Storage
from shared.enums.config_flags import Problem


def main(args):
    cli = Cli(args)
    # logging.warning("Hello, world")
    config = Config.getInstance(None)

    if config.problem == Problem.BIOSCRIPT:
        logging.info("Compiling a BioScript program.")
        problem = BioScript()
    elif config.problem == Problem.MIX:
        logging.info("Running a mix problem")
        problem = Mix()
    elif config.problem == Problem.DISPOSAL:
        logging.info("Running a disposal problem")
        problem = Disposal()
    else:
        logging.info("Running a storage problem")
        problem = Storage()

    problem.run()


if __name__ == '__main__':
    colorlog.basicConfig(level=logging.DEBUG)

    # We don't need the first argument.
    main(sys.argv[1:])

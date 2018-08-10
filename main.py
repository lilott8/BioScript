import logging
import sys
from config.cli import Cli
from config.config import Config
from shared.enums.problem import Problem
from problem.mix import Mix
from problem.storage import Storage
from problem.disposal import Disposal
from problem.bioscript import BioScript
import colorlog


def main(args):
    cli = Cli(args)
    logging.warning("Hello, world")
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
    handler = colorlog.StreamHandler()
    handler.setFormatter(colorlog.ColoredFormatter('%(log_color)s%(levelname)s:[%(name)s%(funcName)@%(lineno)]:%(message)s'))
    colorlog.basicConfig(level=logging.DEBUG)
    # We don't need the first argument.
    main(sys.argv[1:])

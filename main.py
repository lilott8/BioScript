import logging
import sys

import colorlog

from config.cli import Cli
from problem.bioscript import BioScript
from problem.disposal import Disposal
from problem.mix import Mix
from problem.storage import Storage


def main(args):
    # parse the args.
    cli = Cli(args)

    if cli.args.store:
        problem = Storage()
    elif cli.args.disposal:
        problem = Disposal()
    elif cli.args.mix:
        problem = Mix()
    else:
        problem = BioScript()

    problem.run()


if __name__ == '__main__':
    colorlog.basicConfig(level=logging.DEBUG)

    # We don't need the first argument.
    main(sys.argv[1:])

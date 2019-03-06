import logging
import sys

import colorlog

from storage.config.cli import Cli


def main(args):
    # parse the args.
    cli = Cli(args)
    colorlog.log.fatal("Nothing happening in mix, yet")


if __name__ == '__main__':
    colorlog.basicConfig(level=logging.DEBUG)

    # We don't need the first argument.
    main(sys.argv[1:])

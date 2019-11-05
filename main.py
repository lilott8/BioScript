import logging
import sys

import colorlog

from compiler.compiler import BSCompiler
from compiler.config.compiler_cli import CompilerCLI

def main(args):
    # parse the args.
    cli = CompilerCLI(args)
    compiler = BSCompiler(cli.config)
    compiler.compile()


if __name__ == '__main__':
    colorlog.basicConfig(level=logging.DEBUG,
                         format='%(log_color)s%(levelname)s:\t[%(name)s.%(funcName)s:%(lineno)d]\t %(message)s')
    # We don't need the first argument.
    main(sys.argv[1:])

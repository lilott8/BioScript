import logging
import sys

import colorlog

from flow_synth.config.flow_synth_cli import FlowSynthCLI
from flow_synth.flow_synthesizer import FlowSynthesizer


def main(args):
    # parse the args.
    cli = FlowSynthCLI(args)
    synthesizer = FlowSynthesizer(cli.config)
    synthesizer.synthesize()


if __name__ == '__main__':
    colorlog.basicConfig(level=logging.DEBUG,
                         format='%(log_color)s%(levelname)s:\t[%(name)s.%(funcName)s:%(lineno)d]\t %(message)s')

    # We don't need the first argument.
    main(sys.argv[1:])

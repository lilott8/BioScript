import logging
import sys
import argparse


def main(args):
    logging.warning("Hello, world")
    if len(args) == 0:
        logging.error('No args given')
    else:
        logging.info(str(args))



if __name__ == '__main__':
    main(sys.argv)

import argparse
import logging


class Cli(object):

    def __init__(self, args):
        self.log = logging.getLogger()
        self.log.debug(args)

        parser = argparse.ArgumentParser()
        parser.add_argument('-d', '--debug', help='Enable debug mode.', action='store_true')
        parser.add_argument('-l', '--level', help='What level to report errors.', default="error",
                            choices={'error', 'warn', 'none'})
        parser.add_argument('-epa', '--epa-defs', help='Location of EPA definition file.', required=True)

        chemistry = parser.add_argument_group('chemistry', 'Chemistry specific arguments')
        chemistry.add_argument('-s', '--simulate', help='Simulate chemistry.', default=False,
                            choices={True, False}, type=bool)
        chemistry.add_argument('-c', '--classify', help='Chemical classification level.', default=4,
                            choices={0, 1, 2, 4, 8, 16}, type=int)
        chemistry.add_argument('-nf', '--no-filters', help='Disable smart filter creation.', action='store_true')
        chemistry.add_argument('-smarts', '--smarts', help='Length of smart filters to use.', default=5, type=int)

        db_group = parser.add_argument_group('db', 'Database specific arguments:')
        db_group.add_argument('--dbname', help='Name of database.')
        db_group.add_argument('--dbuser', help='Database user.')
        db_group.add_argument('--dbpass', help='Database password for user.')
        db_group.add_argument('--dbaddr', help='Address of database. [IP address | host name]')
        db_group.add_argument('--dbdriver', help='Database driver.', choices={'mysql', 'odbc'})

        self.args = parser.parse_args(args)
        self.validate_config()

    def validate_config(self):
        if self.args.debug:
            self.log.info('Running in debug mode')
        logging.error("Don't forget to validate configs.")

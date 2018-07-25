import argparse
import logging
from config.config import Config


class Cli(object):
    """
    A CLI visitors class.
    Handles building the argsparser and validating the CLI arguments.
    This is the first class to build a config object.  It shouldn't be
    created before this point.
    """

    def __init__(self, args):
        self.log = logging.getLogger(self.__class__.__name__)
        self.log.debug(args)
        self.config = None

        parser = argparse.ArgumentParser()
        required_group = parser.add_argument_group('required', 'Required flags for operations.')
        required_group.add_argument('-epa', '--epa-defs', help='Location of EPA definition file.', required=False)
        required_group.add_argument('-i', '--input', help='json string to validate mixes.', required=True)

        problem_group = parser.add_mutually_exclusive_group(required=True)
        problem_group.add_argument('-s', '--store', help='Is this a storage problem?', action='store_true')
        problem_group.add_argument('-dis', '--disposal', help='Is this a disposal problem?', action='store_true')
        problem_group.add_argument('-m', '--mix', help='Is this a mixing problem?', action='store_true')

        parser.add_argument('-d', '--debug', help='Enable debug mode.', action='store_true', default=False)
        parser.add_argument('-l', '--level', help='What level to report errors.', default="error",
                            choices={'error', 'warn', 'none'})

        chemistry = parser.add_argument_group('chemistry', 'Chemistry specific arguments')
        chemistry.add_argument('-sim', '--simulate', help='Simulate chemistry.', default=False,
                               choices={True, False}, type=bool)
        chemistry.add_argument('-c', '--classify', help='Chemical classification level.', default=4,
                               choices={0, 1, 2, 4, 8, 16}, type=int)
        chemistry.add_argument('-nf', '--no-filters', help='Disable smart filter creation.', action='store_true')
        chemistry.add_argument('-smarts', '--smarts', help='Length of smart filters to use.', default=5, type=int)

        db_group = parser.add_argument_group('db', 'Database specific arguments:')
        db_group.add_argument('--dbname', help='Name of database.', default='')
        db_group.add_argument('--dbuser', help='Database user.')
        db_group.add_argument('--dbpass', help='Database password for user.')
        db_group.add_argument('--dbaddr', help='Address of database. [IP address | host name]', default='localhost')
        db_group.add_argument('--dbdriver', help='Database driver.', choices={'mysql', 'odbc'}, default='mysql')

        self.args = parser.parse_args(args)
        self.validate_config()

        # This should always be the first instantiation of a Config.
        config = Config.getInstance(self.args)
        self.log.warning(config.epa_defs)

    def validate_config(self):
        if self.args.debug:
            self.log.info('Running in debug mode')

        db_enabled = False
        if self.args.dbuser and self.args.dbpass:
            db_enabled = True

        self.config = Config.getInstance(self.args, db_enabled)

        logging.error("Don't forget to validate configs.")

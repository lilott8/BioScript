import argparse

import colorlog

from config.config import Config


class Cli(object):
    """
    A CLI visitors class.
    Handles building the argsparser and validating the CLI arguments.
    This is the first class to build a config object.  It shouldn't be
    created before this point.
    """

    def __init__(self, args):
        self.log = colorlog.getLogger(self.__class__.__name__)
        self.config = None

        parser = argparse.ArgumentParser()

        # problem_group = parser.add_mutually_exclusive_group(required=False)
        # problem_group.add_argument('-s', '--store', help='Is this a storage problem?', action='store_true',
        #                            default=False)
        # problem_group.add_argument('-dis', '--disposal', help='Is this a disposal problem?', action='store_true',
        #                            default=False)
        # problem_group.add_argument('-m', '--mix', help='Is this a mixing problem?', action='store_true', default=False)
        # problem_group.add_argument('-b', '--bioscript', help='Compile a BioScript program.', action='store_true',
        #                            default=True)

        """
        Generic Parser Arguments
        """
        parser.add_argument('-i', '--input', help='input file.', required=True)
        parser.add_argument('-d', '--debug', help='Enable debug mode.', action='store_true', default=False)
        parser.add_argument('-t', '--target', help='Platforms to target.', type=str,
                            default='mfsim', choices={'llvm', 'mfsim', 'puddle', 'inkwell',
                                                      'l', 'm', 'p', 'i'})
        parser.add_argument('-wd', '--working-directory', help="Working path.", default="./", type=str)
        parser.add_argument('-p', '--path', help='What problem are you solving', default='bioscript', type=str,
                            choices={'b', 'bioscript', 'c', 'compile', 'm', 'mix', 'd', 'disposal', 's', 'store'})

        chemistry = parser.add_argument_group('chemistry', 'Chemistry specific arguments')
        chemistry.add_argument('-sim', '--simulate', help='Simulate chemistry.', default=False,
                               choices={True, False}, type=bool)
        chemistry.add_argument('-id', '--identify', help='Chemical identification level.', default=8,
                               choices={0, 1, 2, 4, 8, 16, 32}, type=int)
        chemistry.add_argument('-nf', '--no-filters', help='Disable smart filter creation.', action='store_true')
        chemistry.add_argument('-smarts', '--smarts', help='Length of smart filters to use.', default=5, type=int)

        typing_group = parser.add_argument_group('typing', 'Typing specific arguments')
        typing_group.add_argument('-tcl', '--typechecklevel', help='What level to report errors.', default="error",
                                  choices={'error', 'warn', 'none'})
        typing_group.add_argument('-tc', '--typecheck', help='What level to type check this problem.', default='n',
                                  choices={'n', 'naive', 'u', 'union', 'd', 'disable'})
        typing_group.add_argument('-epa', '--epa-defs', help='Location of EPA definition file.', required=False,
                                  default='./resources/epa.json')
        typing_group.add_argument('-abs', '--abs-int', help="Location for the abstract interaction files.",
                                  required=False, default='./resources/abstract-interaction.txt')

        db_group = parser.add_argument_group('db', 'Database specific arguments:')
        db_group.add_argument('--dbname', help='Name of database.', default='')
        db_group.add_argument('--dbuser', help='Database user.')
        db_group.add_argument('--dbpass', help='Database password for user.')
        db_group.add_argument('--dbaddr', help='Address of database. [IP address | host name]', default='localhost')
        db_group.add_argument('--dbdriver', help='Database driver.', choices={'mysql', 'odbc'}, default='mysql')

        self.args = parser.parse_args(args)
        self.validate_config()

        # This should always be the first instantiation of a Config.
        # config = Config.getInstance(self.args)
        self.log.warning(self.config.input)

    def validate_config(self):
        if self.args.debug:
            self.log.info('Running in debug mode')

        self.config = Config.getInstance(self.args)

        colorlog.error("Don't forget to validate configs.")

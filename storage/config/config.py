import os
import sys

import colorlog


class Config(object):

    def __init__(self, args=None):
        self.log = colorlog.getLogger(self.__class__.__name__)
        """
        General Stuff
        """
        self.debug = False
        self.epa_defs = '/resources/epa_defs.json'
        self.abstract_interaction = '/resources/abstract-interaction.txt'
        self.input = None
        self.input_file = None
        self.validate = False

        """
        Necessary for identify
        """
        self.db_enabled = False
        # Database stuff.
        self.db = {'name': None, 'pass': None, 'addr': None, 'user': None, 'driver': None}

        """
        Build the config object now.
        """
        self.log.warning(args)
        self.debug = args.debug
        self.path = os.path.dirname(sys.modules['__main__'].__file__)

        self.epa_defs = args.epa_defs
        self.abstract_interaction = args.abs_int

        self.input = args.input
        self.validate = args.validate
        # Converts: /path/to/bioscript.bs => bioscript
        self.input_file = args.input.split("/")[-1].split(".")[0]
        # self.log.info(self.input_file)
        self.db['name'] = args.dbname
        self.db['user'] = args.dbuser
        self.db['pass'] = args.dbpass
        self.db['addr'] = args.dbaddr
        self.db['driver'] = args.dbdriver

        if self.db['name'] and self.db['user'] and self.db['pass']:
            self.db_enabled = True
            if not self.db['addr']:
                self.db['addr'] = 'localhost'
            if not self.db['driver']:
                self.db['driver'] = 'mysql'

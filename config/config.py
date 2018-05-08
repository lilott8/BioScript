

class Config(object):
    """
    A singleton config object that allows us to maintain state regardless of
    where it is accessed.  We keep our global configuration state here.
    This ensures we can access at all points of our system.
    """
    __instance = None

    @staticmethod
    def getInstance(args=None, db_enabled=False):
        if Config.__instance is None:
            Config(args, db_enabled)
        return Config.__instance

    def __init__(self, args=None, db_enabled=False):
        self.db_enabled = False
        self.debug = False
        self.epa_defs = './resources/epa_defs.json'
        self.db_name = None
        self.db_pass = None
        self.db_addr = None
        self.db_user = None
        self.db_extras = None
        self.smarts_length = 5
        self.filters = True
        self.classify = 4
        self.simulate = True
        self.error_level = "ERROR"
        if Config.__instance is not None:
            raise Exception('This is a singleton.')
        else:
            self.debug = args.debug
            self.epa_defs = args.epa_defs
            self.db_name = args.dbname
            self.db_pass = args.dbpass
            self.db_addr = args.dbaddr
            self.db_user = args.dbuser
            self.db_driver = args.dbdriver
            self.db_enabled = db_enabled
            self.smarts_length = args.smarts
            self.filters = not args.no_filters
            self.classify = args.classify
            self.simulate = args.simulate
            self.error_level = args.level
            Config.__instance = self

class UndefinedException(Exception):

    def __init__(self, error_message):
        Exception.__init__(self, error_message)

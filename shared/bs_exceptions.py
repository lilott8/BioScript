class UndefinedException(Exception):

    def __init__(self, error_message):
        Exception.__init__(self, error_message)


class IdentificationException(Exception):

    def __init__(self, error_message):
        Exception.__init__(self, error_message)


class InvalidOperation(Exception):

    def __init__(self, error_message):
        Exception.__init__(self, error_message)


class UnsupportedOperation(Exception):

    def __init__(self, error_message):
        Exception.__init__(self, error_message)


class UnsupportedVariable(Exception):

    def __init__(self, error_message):
        Exception.__init__(self, error_message)

import MySQLdb


class Database(object):

    def __init__(self, db: dict):
        self.connection = MySQLdb.connect(host=db['addr'], user=db['user'], passwd=db['pass'], db=db['driver'])

    def close(self):
        self.connection.close()

    def is_connected(self):
        return True if self.connection else False

    def sql_query(self, sql_string):
        cursor = self.connection.cursor()
        cursor.execute(sql_string)
        return cursor

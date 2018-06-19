import MySQLdb

class Database(object):

    def __init__(self, user, password, host, port, db):
        self.connection = MySQLdb.connect(host = host, user = user, passwd = password, db = db)


    def close(self):
        self.connection.close()


    def sql_query(self, sql_string):
        cursor = self.connection.cursor()
        cursor.execute(sql_string)
        return cursor

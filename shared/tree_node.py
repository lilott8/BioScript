class TreeNode(object):

    def __init__(self, value):
        self.value = value
        self.left = None
        self.right = None

    def __str__(self):
        return self.value

    def __repr__(self):
        return "{}".format(self.value)

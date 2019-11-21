from tests.convert.z3_test import *

array = test_z3solver()

for test in array:
    print('TEST')
    for t in test:
        (color, volume) = t
        print('    [BIN] color: %s, volume: %s' % (color, volume))
    print('\n\n')


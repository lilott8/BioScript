import json


def main():

    matrix = dict()

    file = open("resources/epa.json", 'r')
    temp = json.load(file)
    for x in temp['chemicalgroups']['group']:
        #print(temp['chemicalgroups']['group'][x])
        pass

    #print(temp['chemicalgroups']['group'][1]['name'])
    #print(temp['chemicalgroups']['group'][1]['reactivegroups'])
    #print(temp['chemicalgroups']['group'][1]['reactivegroups']['reaction'][0]['id'])
    #print(temp['chemicalgroups']['group'][1]['reactivegroups']['reaction'][0]['outcome'])

    left_id = int(temp['chemicalgroups']['group'][1]['id'])
    right_id = int(temp['chemicalgroups']['group'][1]['reactivegroups']['reaction'][0]['id'])

    matrix[left_id] = dict()
    matrix[left_id][right_id] = temp['chemicalgroups']['group'][1]['reactivegroups']['reaction'][0]['outcome']

    print(matrix[2][3])



if __name__ == "__main__":
    main()
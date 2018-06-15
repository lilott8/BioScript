#convert Java 448-480 lines to python....
#one-to-one conversion might not be possible...depending on how it might be implemented...
#types == set
#def look_up_type(types, reaction_matrix):
#    results = set()
#    for t1 in types:
#        for t2 in types:
#            results.update(look_up_a_b(t1, t2, reaction_matrix))

#    return results


#def look_up_a_b(a, b, reaction_matrix):
#    if a > b:
#        a, b = b, a

#    if a in reaction_matrix and b in reaction_matrix[a]:
#        return map(lambda x: Problem.get_type_from_id(x), reaction_matrix[a][b])
#    else:
#        return {Problem.get_type_from_id(a), Problem.get_type_from_id(b)}
#look_up_type({1, 2}, {1:{2:{3, 4, 5}}})






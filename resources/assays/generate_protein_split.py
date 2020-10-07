import math

# basic script from reverse engineering ProteinSplit_# dags in MFSim's benchmarks

# num = 2^exp (eg. proteinsplit 2 gets exp = 2 for 4 dilution samples)
# this gives us a concentration factor diluting the protein sample
exp = 6
num = 2 ** exp
usein = True
n = 0

with open("output/ProteinSplit_{}.bs".format(exp), mode='w') as file:
    file.write("//protein dilution assay derived from [Su and Chakrabarty, 2008]")
    file.write("\n// we assume volatility of all new mixed constituents, which must be used immediately.")

    file.write("\nmodule sensor")
    file.write("\nmanifest DsS //sample")
    file.write("\nmanifest DsB //buffer")
    file.write("\nmanifest DsR //reagent\n")

    file.write("\ninstructions:")
    if usein:
        file.write("\n@usein {}s".format(n))
    file.write("\nmix1 = mix 10 units of DsS with 10 units of DsB for 3s")
    file.write("\nslt1 = split mix1 into 2")

    for i in range(2, num):
        file.write("\n")
        if usein:
            file.write("\n@usein {}s".format(n))
        file.write("\nmix{} = mix slt{}[{}] with 10 units of DsB for 3s".format(i, math.floor(i / 2), 0 if i % 2 == 0 else 1))
        file.write("\nslt{} = split mix{} into 2".format(i, i))

    for i in range(0, num):
        j = num+i*5
        file.write("\n\n// path {}".format(i+1))
        if usein:
            file.write("\n@usein {}s".format(n))
        file.write("\nmix{} = mix slt{}[{}] with 10 units of DsB for 3s".format(j, math.floor((num+i)/2), 0 if j % 2 == 0 else 1))
        if usein:
            file.write("\n@usein {}s".format(n))

        file.write("\nmix{} = mix mix{} with 10 units of DsB for 3s".format(j+1, j))
        if usein:
            file.write("\n@usein {}s".format(n))

        file.write("\nmix{} = mix mix{} with 10 units of DsB for 3s".format(j+2, j+1))
        if usein:
            file.write("\n@usein {}s".format(n))

        file.write("\nmix{} = mix mix{} with 10 units of DsB for 3s".format(j+3, j+2))
        if usein:
            file.write("\n@usein {}s".format(n))

        file.write("\nmix{} = mix mix{} with 10 units of DsR for 3s".format(j+4, j+3))
        file.write("\ndet{} = detect sensor on mix{} for 30s".format(i+1, j+4))
        file.write("\ndispose mix{}".format(j+4))
    file.write("\n")

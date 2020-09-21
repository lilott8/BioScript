# basic script from reverse engineering InVitro_# dags in MFSim's benchmarks
samples = ["Plasma", "Serum", "Saliva", "Urine"]
reagents = ["Glucose", "Lactate", "Pyruvate", "Glutamate"]
# choose how many samples and reagents
s = 3
r = 4
usein = True
n = 0

with open("output/InVitro_{}s_{}r.bs".format(s, r), mode='w') as file:
    file.write("// protein dilution assay derived from [Su and Chakrabarty, 2008]")
    file.write("\n// we assume volatility of all new mixed constituents, which must be used immediately.")

    file.write("\nmodule sensor")

    for i in range(1, s+1):
        file.write("\nmanifest {}".format(samples[i-1]))

    for i in range(1, r+1):
        file.write("\nmanifest {}".format(reagents[i-1]))

    file.write("\n\ninstructions:")

    count = 1
    for i in range(1, s+1):
        for j in range(1, r+1):
            if usein:
                file.write("\n@usein {}s".format(n))
            file.write("\nmix{} = mix 10 units of {} with 10 units of {} for 5s".format(count, samples[i-1], reagents[j-1]))
            file.write("\ndet{} = detect sensor on mix{} for 5s".format(count, count))
            file.write("\ndispose mix{}\n".format(count))
            count += 1

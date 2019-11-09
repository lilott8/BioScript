from compiler.data_structures import Program
from compiler.passes.analyses.bs_analysis import BSAnalysis
import json
import numpy as np
import networkx as nx
import matplotlib.pyplot as plt
from itertools import count


# Internet code to properly import
try:
    import pygraphviz
    from networkx.drawing.nx_agraph import graphviz_layout
except ImportError:
    try:
        import pydot
        from networkx.drawing.nx_pydot import graphviz_layout
    except ImportError:
        raise ImportError("This example needs Graphviz and either "
                          "PyGraphviz or pydot")

from collections import defaultdict
#TODO: ENSURE YOU HAVE THE ABOVE PACKAGES INSTALLED
# install graphviz package (apt-get) THEN graphviz(pip) or
# Install python-graphviz (That should work)

# Use-def chain
# https://en.wikipedia.org/wiki/Use-define_chain
# https://github.com/lilott8/ChemCompiler-Deprecated-/blob/master/src/main/java/compilation/datastructures/basicblock/DependencySlicedBasicBlock.java

# RUN COMMAND: python3 main.py -i tests/test_cases/slice/slice1.bs -t ir
# Stick to formats that have libraries between languages : JSON recommend
# NetworkX goes away at this stage
# Be aware of certain flow displays of mfsim
# Goals: Build def-use chain, implicitly building the needed DAGs, Dependency Graph

class Chain(object):

    def __init__(self, block: int, instruction: int):
        self.block = -1
        self.instruction = -1


class Slicer(BSAnalysis):

    def __init__(self):
        super().__init__("Slicer")
        self.def_use_chain = dict()

    def analyze(self, program: Program) -> dict:
        self.build_dependency_graph(program)
        self.build_def_use_chain(program)
        return {'name': self.name, 'result': None}

    def build_dependency_graph(self, program: Program):
        deps = dict()
        defs = dict()
        uses = list()  # list of maps
        def_use_json = dict()

        for root in program.functions:
            for nid, block in program.functions[root]['blocks'].items():
                counter = 1
                for instruction in block.instructions:
                    # self.log.info(instruction)
                    # print(instruction)
                    # print(type(instruction))

                    # DISPENSE
                    if str(type(instruction)) == "<class 'compiler.data_structures.ir.Dispense'>":
                        ins = str(instruction).split('=')
                        var = ins[0].strip()
                        exp = ins[1:]

                        deps[var] = exp
                        defs[var] = counter

                    # MIX
                    if str(type(instruction)) == "<class 'compiler.data_structures.ir.Mix'>":
                        ins = str(instruction).split('=')
                        var = ins[0].strip()
                        exp = ins[1:]
                        parts = str(exp)[7:-3].split(',')

                        deps[var] = exp
                        defs[var] = counter
                        uses.extend([(parts[0].strip(), counter), (parts[1].strip(), counter)])

                    # Line Counter
                    counter += 1

        # This aligns out print statements with the log format info = green, warn = yellow, error = red
        self.log.info("\nDeps: \n{} \nDefs: \n{} \nUses: \n{}".format(deps, defs, uses))

        # output data file
        for u in uses:
            def_use_json[u[0]] = "{},{}".format(u[1], defs[u[0]])
        with open('data.txt', 'w') as outfile:
            json.dump(def_use_json, outfile)

        # find the possible conflicts
        used = defaultdict(list)
        for u in uses:
            used[u[0]].append(u[1])
        for root in program.functions:
            pg = program.functions[root]['graph']
            # pg_len = nx.shortest_path_length(pg,)

        ################### Graph Code ##############################
            for n in pg:
                # The actual name 'color' is not needed, we're just getting a numerical
                # Attribute
                self.log.warn(pg[n])

                # n['color'] = 0
            # This does the structural stuff to convert all the values to a colorbar

            groups = set(nx.get_node_attributes(pg, 'color').values())
            mapping = dict(zip(sorted(groups), count()))
            nodes = pg.nodes()
            # If we actually cared about coloring nodes we would do this
            # colors = [mapping[pg.node[n]['color']] for n in nodes]
            # dot - filter
            # for drawing directed graphs
            #
            # neato - filter
            # for drawing undirected graphs
            #
            # twopi - filter
            # for radial layouts of graphs
            #
            # circo - filter
            # for circular layout of graphs
            #
            # fdp - filter
            # for drawing undirected graphs
            #
            # sfdp - filter
            # for drawing large undirected graphs
            #
            # patchwork - filter
            # for tree maps
            pos = graphviz_layout(pg, prog='fdp', args='')
            # Draws Edges
            ec = nx.draw_networkx_edges(pg, pos, alpha=0.2)
            # Draws Nodes
            # If we actually cared about colors, node_color = colors
            nc = nx.draw_networkx_nodes(pg, pos, nodelist=nodes, node_color="blue",
                                        with_labels=False, node_size=10, cmap=plt.cm.jet)
        plt.colorbar(nc)
        plt.axis('off')
        plt.show()
        # This might be helpful if you need higher quality, also available in pdf
        #plt.savefig('slice.png')
        ##############################################################

        self.log.warn("\npossible multi-uses:")
        for u in used:
            if len(used[u]) > 1:
                self.log.warn("{} in block: 0 at line: {} ".format(u, used[u][1:]))

        return [deps, defs, uses]

    def build_def_use_chain(self, root: str):
        pass



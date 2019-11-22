from colorlog import logging

from compiler.data_structures import Program
from compiler.data_structures import IRInstruction
from compiler.passes.analyses.bs_analysis import BSAnalysis

import json
import networkx as nx
import matplotlib.pyplot as plt
from collections import defaultdict
from itertools import count
import colorlog.logging

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


# NOTE: ENSURE YOU HAVE THE ABOVE PACKAGES INSTALLED
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


class Slicer(BSAnalysis):

    def __init__(self):
        super().__init__("Slicer")
        self.multi_use = dict()

    def analyze(self, program: Program) -> dict:
        self.multi_use = self.build_def_use_chain(program)
        return {'name': self.name, 'result': None}

    def build_def_use_chain(self, program: Program) -> dict:
        # Trust me, keep this line
        # Needs colorlog.logging I believe, I used pycharm to import
        logging.getLogger('matplotlib.font_manager').disabled = True

        deps = dict()
        defs = dict()
        uses = list()
        used = defaultdict(list)
        many_use = defaultdict(list)
        mini_use = defaultdict(set)
        total = dict()

        for root in program.functions:
            self.log.info("Function: {}".format(root))

            # sorted blocks so always same order each time
            for nid, block in sorted(program.functions[root]['blocks'].items()):
                i_counter = 1
                self.log.info("\tBlock: {}".format(nid))

                for instruction in block.instructions:
                    self.log.info("\t\t{}".format(instruction))

                    # DEF: DISPENSE, ...
                    if instruction.op == IRInstruction.DISPENSE:
                        ins = str(instruction).split('=')
                        var = ins[0].strip()
                        exp = ins[1:]

                        deps[var] = exp
                        defs[var] = (nid, i_counter)

                    # USE && DEF: MIX, HEAT, SPLIT, ... CALL?
                    if instruction.op == IRInstruction.MIX:
                        ins = str(instruction).split('=')
                        var = ins[0].strip()
                        exp = ins[1:]
                        parts = str(exp)[7:-3].split(',')

                        deps[var] = exp
                        defs[var] = (nid, i_counter)
                        uses.extend([(parts[0].strip(), (nid, i_counter)), (parts[1].strip(), (nid, i_counter))])

                    if instruction.op == IRInstruction.CALL:
                        ins = str(instruction).split('=')
                        var = ins[0].strip()
                        fun = instruction.name
                        user = list()
                        for u in instruction.uses:
                            user.append(u['name'])
                        exp = fun + '(' + ','.join(user) + ')'

                        deps[var] = exp
                        defs[var] = (nid, i_counter)
                        for u in user:
                            uses.append( (u.strip(), (nid, i_counter)) )

                    # Line Counter
                    i_counter += 1

            # -------------------- Graph Code -------------------- #
            #         pg = program.functions[root]['graph']
            #         nodes = pg.nodes()
            #
            # pos = graphviz_layout(pg, prog='dot', args='')
            # # Draws Edges
            # ec = nx.draw_networkx_edges(pg, pos, alpha=0.2)
            # # Draws Nodes
            # # If we actually cared about colors, node_color = colors
            # nc = nx.draw_networkx_nodes(pg, pos, nodelist=nodes, node_color="blue",
            #                             with_labels=True, node_size=10, cmap=plt.cm.jet)
            #
            # labels = dict()
            # for i in range(1, len(nodes)+1):
            #     labels[i] = str(i)
            # nx.draw_networkx_labels(pg, pos, labels, font_size=16)
            #
            # plt.colorbar(nc)
            # plt.axis('off')
            # # plt.show()
            # # This might be helpful if you need higher quality, also available in pdf
            # plt.savefig('slice.png')
            # -------------------- Graph Code -------------------- #

        # TODO: figure out with loops, and functions
        # find the possible conflicts
        for u in uses:
            used[u[0]].append(u[1])
        for u in used:
            # check if multi use occurred one after the other,
            # but not on the same level like in an if/else
            if len(used[u]) > 1:
                blks = list()
                for x in used[u]:
                    blks.append(x[0])
                many_use[u] = used[u]  # adds all uses, but usually need the last ones

        # take the union of the extra uses on each path
        # if 2 edges goto same node and both use a variable, mark the variable as used
        # if encountered again, then add
        for root in program.functions:
            pg = program.functions[root]['graph']
            start = list(pg.nodes())[0]
            finish = list(pg.nodes())[-1]  # initially set to the end
            print("nodes: ", pg.nodes())
            print(root, list(sorted(program.functions[root]['blocks'].items())))
            for nid, block in sorted(program.functions[root]['blocks'].items()):
                for b in block.instructions:
                    try:
                        if b.op == IRInstruction.NOP:
                            print(nid, block)
                            finish = list(pg.nodes())[nid-1]
                    except:  # out of range errors?
                        print(__import__('sys').exc_info())
                        print("SLICE NOP HELP!!", nid, list(pg.nodes()))
                        finish = start
                        pass  # FIXME

            # all paths from entry to end of block
            paths = list(nx.all_simple_paths(pg, start, finish))
            print(paths)
            if paths == list():  # special case for straight line programs
                paths = [[1]]
            for var in many_use:             # each func
                for p in paths:              # each path
                    first_u = False
                    for x in many_use[var]:  # each use
                        if x[0] in p and first_u:
                            mini_use[var].add(x)
                        if x[0] in p and not first_u:
                            first_u = True

        # var : (instructions, position)
        total['Double-Use Instructions'] = []
        for m in mini_use:
            remake = [d.strip() for d in deps[m]]
            total['Double-Use Instructions'].append({
                'Variable Name': m,
                'Define-Instruction': remake,
                'Use-Instruction (Block, Line)': list(mini_use[m])})

        # print statements with the log format info = green, warn = yellow, error = red
        self.log.info("\nDeps: \n{} \nDefs: \n{} \nUses: \n{} \nUsed:  \n{} \nMulti-Used: \n{}\nMini-Used: \n{}\nFinal: \n{}"
                      .format(deps, defs, uses, dict(used), dict(many_use), dict(mini_use), total))

        # output JSON data file
        with open('data.json', 'w') as outfile:
            json.dump(total, outfile)

        return total


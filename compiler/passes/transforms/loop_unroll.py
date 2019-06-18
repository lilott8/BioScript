from compiler.data_structures import BinaryOps
from compiler.data_structures.program import Program
from compiler.passes.transforms.bs_transform import BSTransform
import networkx as nx


class LoopUnroll(BSTransform):

	def __init__(self):
		super().__init__("LoopUnravel")
		self.log.warn("Hello World")

	#Function:
	#1) Assign - Use Cycle to find parent, child, end
	#2) Identify - Find Multiplicity in Parent(The number of times we run the loop)
	#3) Execute
	#	ex: while(x < Parent.Multiplicity)
	#			Child += Child
	#		x + = 1
	#		Child+=End
	#) Clean-Up
	#		Child.incomingEdges += Parent.incoming edges (Loop-through,external to the cycle ofc)
	#		Remove Parent
	#		Child.outgoing += End.outgoing ( Loop through ,external to the cycle)
	#		Remove End
	# Just assumes second item is the reverse edge
	def unroll(self, program: Program):
			for root in program.functions:
				self.log.warn(program.functions[root]['graph'])
				try:
					glist = list(nx.find_cycle(program.functions[root]['graph']))
				except:
					self.log.warn("No Cycles Found")

				child = int(glist[1][0])
				parent = glist[1][1]
				#root[child] = root[child] + root[child]
				#del(root[parent])
				#Remove the jumps from the child to the parent
				#Find the multiplier in the parent
				#"Multiply" the instruction in the child
				# Edge Cases
				# 1) variable to constant, variable doesn't change
				# 2) variable to variable ,neither change
				# 3) variable to constant, wrong direction
				###################################################33

				# Pops Jump
				jump = program.functions[root]['blocks'][child].instructions.pop(2)
				BO = program.functions[root]['blocks'][child].instructions.pop(1)
				if 	BinaryOps.SUBTRACT == BO.op :
					pass
				else:
					return
				reducer = BO.right

				#Find the constant and find the false-jump

				label = program.functions[root]['blocks'][parent].instructions.pop(1)
				#constant = label.right
				constant = 8
				jump.jumps = label.false_branch
				old = program.functions[root]['blocks'][child].instructions[0]
				while constant > 0:
					program.functions[root]['blocks'][child].instructions.append(old)
					constant -= 1
				program.functions[root]['blocks'][child].instructions.append(jump)
				program.functions[root]['blocks'].pop(parent)






				# Pops the X Modifer instruction
				#Str_Value =	" " + program.functions[root]['blocks'][child].instructions.pop(1)
				#Gets X Modifer
				#value_list = Str_Value.split()
				#reducer = value_list[-1]
				#self.log.warn(reducer)


				#self.log.warn(program.functions[root]['blocks'][child])



			for root in program.functions:
				for block in program.functions[root]['blocks']:
							self.log.warn(program.functions[root]['blocks'][block])






#Entry Point
	def transform(self, program: Program) -> Program:
		self.unroll(program)

		return program


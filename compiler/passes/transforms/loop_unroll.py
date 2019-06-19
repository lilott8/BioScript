from compiler.data_structures import *
from compiler.data_structures.program import Program
from compiler.passes.transforms.bs_transform import BSTransform
import networkx as nx



class LoopUnroll(BSTransform):

	def __init__(self):
		super().__init__("LoopUnravel")
		self.log.warn("Starting Loop Unrolling.....")


	def unroll(self, program: Program) -> Program:
			global jump
			for root in program.functions:
				try:
					glist = list(nx.find_cycle(program.functions[root]['graph']))
				except:
					self.log.warn("No Loops Found. No need to unroll")
					return program #No Cycles to unroll!


				child = glist[1][0]
				parent =glist[1][1]

				# Loop Unroll Algorithm
				# Find Variables in  Block 1
				# Detect Usage in Block 2 (Instruction with a BinaryOP on variable)
				# Detect if BinaryOp follows protocol
				# If so, unroll loop nicely

				# TODO : Get Left variable on jump condition
				# TODO:  Better Jump Detect Algorithm, find variable from parent in child

				# This label is the conditional on the parent....
				# We loop through all conditionals, find the last (that will be the last argument anyway)
				# Search that conditional for a variable, store the variable as an object
				#Remove the last condition (loop header)

				##IDENTIFY
				#PARENT MODIFICATIONS
				#label = None
				for items in program.functions[root]['blocks'][parent].instructions:
					if type(items) == Conditional:
						self.log.warn("Success")
						label = program.functions[root]['blocks'][parent].instructions.pop(
							program.functions[root]['blocks'][parent].instructions.index(items))
						l_left = label.left
						l_right = label.right
					else:
						self.log.warn(type(items))
				# Remove Jumps
				self.log.warn(label )
				#CHILD MODIFICATIONS
				jump = program.functions[root]['blocks'][child].instructions.pop(-1)
				for items2 in program.functions[root]['blocks'][child].instructions:

					if type(items2) == BinaryOp:
						self.log.warn("Success")
						BO = program.functions[root]['blocks'][child].instructions.pop(
							program.functions[root]['blocks'][child].instructions.index(items2))
					else:
						self.log.warn(items2)
						self.log.warn(type(items2))
			#	self.log.warn(jump + "Henlo" )
				self.log.warn(BO)

				#EXECUTE
				if BinaryOps.SUBTRACT == BO.op:

					reducer = BO.right

					#Find the constant and find the false-jump

					# TODO: Better Jump Condition Detect
					#constant = label.right
					constant = 8
					base_instructions = program.functions[root]['blocks'][child].instructions.copy()
					while constant > 1:
						program.functions[root]['blocks'][child].instructions.extend(base_instructions)
						constant -= 1
				elif  BinaryOps.ADD == BO.op:
					reducer = BO.right

					# Find the constant and find the false-jump

					# TODO: Better Jump Condition Detect
					# TODO: FIX NUMBER CITIZENSHIP
					# constant = label.right
					constant = 1

					base_instructions = program.functions[root]['blocks'][child].instructions.copy()
					while constant < 7:
						program.functions[root]['blocks'][child].instructions.extend(base_instructions)
						constant += 1
				elif BinaryOps.MULTIPLE == BO.op:
						pass
				elif BinaryOps.DIVIDE == BO.op:
						pass
				else:
					self.log.warn("Control Logic Detected... Aborting Unroll")

				#CLEANUP: Pops Parent, adds jump, redoes the labels.
				jump.jumps = label.false_branch
				program.functions[root]['blocks'][child].instructions.append(jump)
				program.functions[root]['blocks'].pop(parent)
				program.functions[root]['blocks'][child].label = label.true_branch
				program.functions[root]['blocks'][child].jumps.pop()


			#Test code showing program post unroll
			for root in program.functions:
				for block in program.functions[root]['blocks']:
							self.log.warn(program.functions[root]['blocks'][block])
			self.log.warn("Loop Unrolling Completed")
			return program




#Entry Point
	def transform(self, program: Program) -> Program:
		#Test Print to show pre-unroll
		for root in program.functions:
			for block in program.functions[root]['blocks']:
				self.log.warn(program.functions[root]['blocks'][block])
		#Test function
		return self.unroll(program)


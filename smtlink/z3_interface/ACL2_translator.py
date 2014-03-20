from z3 import Solver, Bool, Int, Real, BoolSort, IntSort, RealSort, And, Or, Not, Implies, unsat

def boolClass():
	x = True
	return x.__class__

def intClass():
	x = 0
	return x.__class__

def realClass():
	x = 0.0
	return x.__class__

def sort(x):
	if x.__class__ == boolClass(): return(BoolSort())
	if x.__class__ == intClass():  return(IntSort())
	if x.__class__ == realClass(): return(RealSort())
	try: return x.sort() 
	except AttributeError:
		raise Exception('unknown sort for expression')

class to_smt:
	class status:
		def __init__(self, value):
			self.value = value

		def __str__(self):
			if(self.value is True): return 'QED'
			elif(self.value.__class__ == 'msg'.__class__): return self.value
			else: raise Exception('unknown status?')

		def isThm(self):
			return(self.value is True)


	def __init__(self, solver=0):
		if(solver != 0): self.solver = solver
		else: self.solver = Solver()
		self.nameNumber = 0

	def newVar(self):
		varName = '$' + str(self.nameNumber)
		self.nameNumber = self.nameNumber+1
		return varName

	def plus(self, *args):
		sum = 0
		for a in args:
			sum = sum + a
		return sum

	def isBool(self, who):
		return Bool(who)

	def isInt(self, who):
		return Int(who)

	def isReal(self, who):
		return Real(who)

	def multiply(self, *args):
		product = 1
		for a in args:
			product = product * a
		return product

	def andx(self, *args):
		conjunction = True
		for a in args:
			conjunction = And(conjunction, a)
		return conjunction

	def orx(self, *args):
		disjunction = False
		for a in args:
			disjunction = Or(disjunction, a)
		return disjunction

	def minus(self, x,y): return x-y
	def divide(self, x,y): return x/y
	def gt(self, x,y): return x>y
	def lt(self, x,y): return x<y
	def ge(self, x,y): return x>=y
	def le(self, x,y): return x<=y
	def equal(self, x,y): return x==y
	def notx(self, x): return Not(x)

	def ifx(self, condx, thenx, elsex):
		v = 0
		if sort(thenx) == sort(elsex):
			if sort(thenx) == BoolSort(): v = Bool(self.newVar())
			if sort(thenx) == IntSort():  v = Int(self.newVar())
			if sort(thenx) == RealSort(): v = Real(self.newVar())
		if v is 0: raise Exception('mixed type for if-expression')
		self.solver.add(And(Implies(condx, v == thenx), Implies(Not(condx), v == elsex)))
		return(v)

# usage prove(claim) or prove(hypotheses, conclusion)
	def prove(self, hypotheses, conclusion=0):
		if(conclusion is 0): claim = hypotheses
		else: claim = Implies(hypotheses, conclusion)
		self.solver.add(Not(claim))
		if self.solver.check() == unsat:
                        print "proved"
                        return self.status(True)  # It's a theorem
		else:
                        print "failed to prove"
                        return self.status(str(self.solver.model())) # provide a counter-example string

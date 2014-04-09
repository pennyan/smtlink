from z3 import Solver, Bool, Int, Real, BoolSort, IntSort, RealSort, And, Or, Not, Implies, sat, unsat

def sort(x):
  if type(x) == bool:    return BoolSort()
  elif type(x) == int:   return IntSort()
  elif type(x) == float: return RealSort()
  elif (type(x) == instance) & hasattr(x, 'sort'):
    if x.sort() == BoolSort(): return BoolSort()
    if x.sort() == IntSort():  return IntSort()
    if x.sort() == RealSort(): return RealSort()
  raise Exception('unknown sort for expression')

def makeOne(x):
  s = sort(x)
  if(s == BoolSort): return Bool
  if(s == IntSort):  return Int
  if(s == RealSort): return Real
  else:
    raise Exception('unknown sort for expression')

class to_smt:
  # a class for getting the status wrapping up status of z3 output
  class status:
    def __init__(self, value):
      self.value = value

    def __str__(self):
      if(self.value is True): return 'QED'
      elif(self.value.__class__ == 'msg'.__class__): return self.value
      else: raise Exception('unknown status?')

    def isThm(self):
      return(self.value is True)

  myVars = {} # variables: (string : z3_variables) pairs
  claim = None
        
  def __init__(self, solver=0):
    if(solver != 0): self.solver = solver
    else: self.solver = Solver()
    self.nameNumber = 0

  def newVar(self):
    varName = '$' + str(self.nameNumber)
    self.nameNumber = self.nameNumber+1
    return varName

  def isBool(self, who): self.declare(who, Bool)
  def isInt(self, who):  self.declare(who, Int)
  def isReal(self, who): self.declare(who, Real)

  def declare(self, name, MakeOne)
    if name in self.v:
      raise Exception(name + ' already declared')
    newvar = MakeOne(name)
    self.myVars[name] = newvar
    return newvar

  def plus(self, *args):
    return reduce(lambda x, y: x+y, args)
  def times(self, *args):
    return reduce(lambda x, y: x*y, args)
  def andx(self, *args):
    return reduce(lambda x, y: And(x,y), args)
  def orx(self, *args):
    return reduce(lambda x, y: Or(x,y), args)

  def minus(self, x,y): return x-y
  def reciprocal(self, x): return 1/x
  def div(self, x, y): return times(self,x,reciprocal(self,y))
  def gt(self, x,y): return x>y
  def lt(self, x,y): return x<y
  def ge(self, x,y): return x>=y
  def le(self, x,y): return x<=y
  def equal(self, x,y): return x==y
  def notx(self, x): return Not(x)

  def ifx(self, condx, thenx, elsex):
    v = None
    if sort(thenx) == sort(elsex):
      v = self.declare(self.newVar(), makeOne(thenx))
    if v is None: raise Exception('mixed type for if-expression')
    self.solver.add(And(Implies(condx, v == thenx), Implies(Not(condx), v == elsex)))
    return v

  # stuff.let(['x', 2.0], ['y', v('a')*v('b') + v('c')], ['z', ...]).inn(2*v('x') - v('y'))
  def let(self, bindingList):
    for b in bindingList:
      self.solver.add(self.declare(b[0], makeOne(b[1])) == b[1])
    return self

  def inn(self, x): return x

  def getVar(self, name):
    return self.myVars[name]

  # Newly added version from Mark's acl2.py
  def implies(self, p, q): return z3.Impies(p,q)
  ####

  def claim(self, p):
    self.claim = p
    self.solver.add(Not(p))

  def prove2(self):
    if self.claim is None:
      raise Exception('prove: no claim')
    return(self.solver.check() == unsat)

  def cex(self):
    m = self.solver.model()
    str = None
    for v in m:
      if str is not None: str = str + ', '
      else: str = ''
      str = str + v.name() + ' = ' + m[v].as_string()
    return(str)

  def reset(self):
    self.solver = Solver()
    self.v = {}
    claim = None
    
  # usage prove(claim) or prove(hypotheses, conclusion)
  def prove(self, hypotheses, conclusion=0):
    if(conclusion is 0): claim = hypotheses
    else: claim = Implies(hypotheses, conclusion)

    self.solver.add(Not(claim))
    res = self.solver.check()

    if res == unsat:
      print "proved"
      return self.status(True)  # It's a theorem
    elif res == sat:
      print "counterexample"
      m = self.solver.model()
      print m
      # return an counterexample??
      return self.status(False) 
    else:
      print "failed to prove"
      return self.status(False)

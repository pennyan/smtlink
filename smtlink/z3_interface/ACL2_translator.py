from z3 import Solver, Bool, Int, Real, BoolSort, IntSort, RealSort, And, Or, Not, Implies, sat, unsat

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

  v = {} # variables: (string : z3_variables) pairs
  claim = None
        
  def __init__(self, solver=0):
    if(solver != 0): self.solver = solver
    else: self.solver = Solver()
    self.nameNumber = 0

  def newVar(self):
    varName = '$' + str(self.nameNumber)
    self.nameNumber = self.nameNumber+1
    return varName

  # Newly added version from Mark's acl2.py
  def implies(self, p, q): return z3.Or(z3.Not(p),q)
  def equals(self, p, q): return p == q
  ####
        
  def plus(self, *args):
    return reduce(lambda x, y: x+y, args)

  def isBool(self, who):
    return Bool(who)

  def isInt(self, who):
    return Int(who)

  def isReal(self, who):
    return Real(who)

  ## rename from multiply to times
  def times(self, *args):
    return reduce(lambda x, y: x*y, args)
  ####
        
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
  def reciprocal(self, x): return 1/x
  def div(self, x, y): return times(self,x,reciprocal(self,y))
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

  def bind(self, name, expr):
  # create a z3 variable according to the sort of expr
    if name in self.v:
      raise Exception(name + ' already declared')
    newvar = None
    if(hasattr(expr, 'sort')):
      if(sort(expr) == BoolSort()):
        newvar = Bool(name)
      elif(sort(expr) == IntSort()):
        newvar = Int(name)
      elif(sort(expr) == RealSort()):
        newvar = Real(name)
      if newvar is not None:
        self.solver.add(newvar == expr)
    elif(expr == BoolSort()):
      newvar = Bool(name)
    elif(expr == IntSort()):
      newvar = Int(name)
    elif(expr == RealSort()):
      newvar = Real(name)
    if newvar is None:
      raise Exception('unknown sort for expression')
    self.v[name] = newvar
    return(self)

  def getvar(self, name):
    return self.v[name]

  def val(self, x): return x

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

import z3

def implies(p, q): return z3.Or(z3.Not(p), q)
def equals(p, q): return p == q
def plus(*args): return reduce(lambda x, y: x+y, args)
def minus(a, b): return a-b
def times(*args): return reduce(lambda x, y: x*y, args)
def div(a, b): return a/b

def BoolSort(): return z3.BoolSort()
def IntSort():  return z3.IntSort()
def RealSort(): return z3.RealSort()


class HandyStuff:
  s = z3.Solver()  # the SMT solver
  v = {}           # variables: (string : z3_variables) pairs
  claim = None

  def bind(self, name, expr):
    # create a z3 variable according to the sort of expr
    if name in self.v:
      raise Exception(name + ' already declared')
    newvar = None
    if(hasattr(expr, 'sort')):
      if(expr.sort() == z3.BoolSort()):
        newvar = z3.Bool(name)
      elif(expr.sort() == z3.IntSort()):
        newvar = z3.Int(name)
      elif(expr.sort() == z3.RealSort()):
        newvar = z3.Real(name)
      if newvar is not None:
        self.s.add(newvar == expr)
    elif(expr == z3.BoolSort()):
      newvar = z3.Bool(name)
    elif(expr == z3.IntSort()):
      newvar = z3.Int(name)
    elif(expr == z3.RealSort()):
      newvar = z3.Real(name)
    if newvar is None:
      raise Exception('unknown sort for expression')
    self.v[name] = newvar
    return(self)

  def getvar(self, name):
    return self.v[name]

  def val(self, x): return x

  def claim(self, p):
    self.claim = p
    self.s.add(z3.Not(p))

  def prove(self):
    if self.claim is None:
      raise Exception('prove: no claim')
    return(self.s.check() == z3.unsat)

  def cex(self):
    m = self.s.model()
    str = None
    for v in m:
      if str is not None: str = str + ', '
      else: str = ''
      str = str + v.name() + ' = ' + m[v].as_string()
    return(str)

  # We don't provide a constructor.  We probably should, but I just wrote
  # this to try my ideas for 'let' expressions.  In Python, if there's no
  # explicit constructor, each call to acl2.HandyStuff() returns a reference
  # to the same object.  I vaguely recall reading about this at some point.
  # Even though it seems quirky, it's handy here for debugging.  I can run
  # my script to try an example.  If it fails, I can call acl2.HandyStuff()
  # and get the solver and declarations, etc., to figure out what happened.
  # On the other hand, trying a new example would require quitting python
  # and starting over.  This reset() method should get us a fresh solver
  # and erase the variable bindings.
  def reset(self):
    self.s = z3.Solver()
    self.v = {}
    claim = None

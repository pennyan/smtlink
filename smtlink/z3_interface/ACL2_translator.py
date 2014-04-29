from z3 import Solver, Bool, Int, Real, BoolSort, IntSort, RealSort, And, Or, Not, Implies, sat, unsat, Q, Array, Select, Store

def sort(x):
    if type(x) == bool:    return BoolSort()
    elif type(x) == int:   return IntSort()
    elif type(x) == float: return RealSort()
    elif hasattr(x, 'sort'):
        if x.sort() == BoolSort(): return BoolSort()
        if x.sort() == IntSort():  return IntSort()
        if x.sort() == RealSort(): return RealSort()
        else:
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

    def isBool(self, who):
        return Bool(who)

    def isInt(self, who):
        return Int(who)

    def isReal(self, who):
        return Real(who)

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
    def negate(self, x): return -x
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

    # array
    def array(self, mylist):
        if not mylist:
           raise("Can't determine type of an empty list.")
        else:
            ty = sort(mylist[0])
            a = Array(self.newVar(), IntSort(), ty)
            n = len(mylist)
            for i in range(0,n):
                j = Int(self.newVar())
                self.solver.add(j == i)
                self.solver.add(Select(a, j) == mylist[i])
        return a
    
    # nth
    def nth(self, i, a):
        return Select(a, i)

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

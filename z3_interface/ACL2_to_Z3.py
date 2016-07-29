# Copyright (C) 2015, University of British Columbia
# Written (originally) by Mark Greenstreet (13th March, 2014)
#
# License: A 3-clause BSD license.
# See the LICENSE file distributed with this software

from z3 import *# Solver, Bool, Int, Real, BoolSort, IntSort, RealSort, And, Or, Not, Implies, sat, unsat, Array, Select, Store, ToInt, Q, If

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

class ACL22SMT(object):
    class status:
        def __init__(self, value):
            self.value = value

        def __str__(self):
            if(self.value is True): return 'QED'
            elif(self.value.__class__ == 'msg'.__class__): return self.value
            else: raise Exception('unknown status?')

        def isThm(self):
            return(self.value is True)

    class atom:  # added my mrg, 21 May 2015
        def __init__(self, string):
            self.who_am_i = string.lower()
        def __eq__(self, other):
            return(self.who_am_i == other.who_am_i)
        def __ne__(self, other):
            return(self.who_am_i != other.who_am_i)
        def __str__(self):
            return(self.who_am_i)

    def __init__(self, solver=0):
        if(solver != 0): self.solver = solver
        else: self.solver = Solver()
        self.nameNumber = 0

    def newVar(self):
        varName = '$' + str(self.nameNumber)
        self.nameNumber = self.nameNumber+1
        return varName

    def isBool(self, who): return Bool(who)
    def isInt(self, who): return Int(who)
    def isReal(self, who): return Real(who)
    def plus(self, *args): return reduce(lambda x, y: x+y, args)
    def times(self, *args): return reduce(lambda x, y: x*y, args)

    def reciprocal(self, x):
        if(type(x) is int): return(Q(1,x))
        elif(type(x) is float): return 1.0/x
        else: return 1.0/x

    def negate(self, x): return -x
    def lt(self, x,y): return x<y
    def equal(self, x,y): return x==y
    def notx(self, x): return Not(x)
    def implies(self, x, y): return Implies(x,y)
    def Qx(self, x, y): return Q(x,y)

    # type related functions
    def integerp(self, x): return sort(x) == IntSort()
    def rationalp(self, x): return sort(x) == RealSort()
    def booleanp(self, x): return sort(x) == BoolSort()

    def ifx(self, condx, thenx, elsex):
        return If(condx, thenx, elsex)

    # # usage prove(claim) or prove(hypotheses, conclusion)
    # def prove(self, hypotheses, conclusion=0):
    #     if(conclusion is 0): claim = hypotheses
    #     else: claim = Implies(hypotheses, conclusion)

    #     self.solver.push()
    #     self.solver.add(Not(claim))
    #     res = self.solver.check()

    #     if res == unsat:
    #         print "proved"
    #         return self.status(True)  # It's a theorem
    #     elif res == sat:
    #         print "counterexample"
    #         m = self.solver.model()
    #         print m
    #         # return an counterexample
    #         return self.status(False)
    #     else:
    #         print "failed to prove"
    #         r = self.status(False)

    #     self.solver.pop()
    #     return(r)

    def proof_success(self):
        print "proved"

    # finds variable names
    def var_lst (self, lst, ret):
        llen = len(lst)
        i = 0
        while i < llen:
            if lst[i].children() == []:
                st = str(lst[i]).replace("-", "").replace(".","").replace("/", "")
                if not st.isdigit():
                    ret.append(st)
            else:
                if isinstance(lst[i].children(),list):
                    self.var_lst (lst[i].children(), ret)
            i += 1
        return list(set(ret));

    # concatonate
    def conc_var_lst (self, st, lst):
        le = len(lst)
        m = self.solver.model()
        i = 0
        while i < le:
            if (st.find("("+lst[i]+" ") == -1) and not(lst[i] == 'False') and not(lst[i] == 'True'):
                if is_bool(eval(lst[i])):
                    st = st + " ("+lst[i]+" (cex-trivial nil))"
                else:
                    st = st + " ("+lst[i]+" (cex-trivial 0))"
            i += 1
        return st

    def pymodel_to_lisp(self):
        m = self.solver.model()
        l = len(m)
        s = ""
        i = 0
        while i < l:
            if (is_rational_value(m[m[i]])) or (is_bool(m[m[i]])):
                val_str = str(m[m[i]]).replace(".0", "").replace("False", "nil").replace("True","t")
                s = s + " (" + str(m[i]) + " " + val_str + ")"
            else:
                rt_obj = str(m[m[i]].sexpr())
                rt_obj = rt_obj.replace("root-obj", "cex-root-obj " + "'" + str(m[i]) + " state")
                rt_obj = rt_obj.replace("(+", "'(+")
                s = s + " (" + str(m[i]) + " " + rt_obj + ")"
            i = i + 1
        return s

    def parse_cex (self, st):
        s1 = st.replace("() ", "")
        s2 = s1.replace("define-fun ", "")
        s3 = s2.replace("Real", "")
        s3 = s3.replace(".0", "")
        s4 = s3.split()
        s5 = ' '.join(s4)
        return s5

    def proof_counterExample(self):
        thing = self.pymodel_to_lisp()

        m = self.solver.model()
        a = self.solver.assertions()
        s0 = m.sexpr()
        s5 = self.pymodel_to_lisp()
        alst = self.var_lst(a, [])
        s6 = self.conc_var_lst(s5, alst)
        print "(" +  s6 + ")"

    def proof_fail(self):
        print "failed to prove"

    # usage prove(claim) or prove(hypotheses, conclusion)
    def prove(self, hypotheses, conclusion=0):
        if(conclusion is 0): claim = hypotheses
        else: claim = Implies(hypotheses, conclusion)

        self.solver.push()
        self.solver.add(Not(claim))
        res = self.solver.check()

        if res == unsat: self.proof_success()
        elif res == sat: self.proof_counterExample()
        else: self.proof_fail()

        self.solver.pop()
        return(self.status(res == unsat))



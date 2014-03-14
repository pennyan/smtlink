import sys
sys.path.insert(0,"../../z3_interface")
from ACL2_translator import *
SIMPLECONST=1
def SIMPLEFUN3(): return 1
def SIMPLEFUN2(X): return acl2_multiply(X,X)
def SIMPLEFUN1(X,Y): return acl2_minus(acl2_multiply(2,SIMPLEFUN2(X),SIMPLECONST),acl2_multiply(SIMPLEFUN3(),X,Y))
X=Real("X")
Y=Real("Y")
hypothesis=acl2_and(acl2_and(acl2_not(acl2_set(X,0))),acl2_gt(X,Y))
conclusion=acl2_gt(SIMPLEFUN1(X,Y),0)
prove(Implies(hypothesis, conclusion))

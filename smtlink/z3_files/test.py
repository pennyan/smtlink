import sys
sys.path.insert(0,"../z3_interface")
from ACL2_translator import *
SIMPLECONST=1
X=Real("X")
Y=Real("Y")
hypothesis=acl2_and(acl2_and(acl2_not(acl2_set(X,0))),acl2_gt(X,Y))
conclusion=acl2_set(acl2_multiply(X,X),acl2_multiply(X,Y,SIMPLECONST))
prove(Implies(hypothesis, conclusion))

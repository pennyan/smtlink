import sys
sys.path.insert(0,"z3_interface")
from ACL2_translator import *
CONST1=1
X=Real("X")
Y=Real("Y")
Z=Real("Z")
hypothesis=acl2_if(False,acl2_if(acl2_equal(Z,acl2_plus(2,4)),acl2_if(acl2_lt(Y,X),acl2_lt(Y,X),acl2_lt(acl2_plus(Y,1),X)),False),False)
conclusion=acl2_lt(acl2_multiply(X,Y),acl2_multiply(X,acl2_multiply(X,Z)))
prove(Implies(And(hypothesis,if_constraint_bool), conclusion))

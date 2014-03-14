from ACL2_translator import *
SIMPLECONST=1
def SIMPLEFUN3():return 1
def SIMPLEFUN2(X):return acl2_multiply(X,X)
def SIMPLEFUN(X,Y):return acl2_minus(acl2_multiply(2,SIMPLEFUN2(X),SIMPLECONST),acl2_multiply(SIMPLEFUN3(),X,Y))
X=Real("X")
Y=Real("Y")
conditions=acl2_and(acl2_and(acl2_not(acl2_set(X,0))),acl2_gt(X,Y))
conclusion=acl2_gt(SIMPLEFUN(X,Y),0)
prove(Implies(conditions,conclusion))

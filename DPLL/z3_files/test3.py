from sys import path
path.insert(0,"/ubc/cs/home/y/yanpeng/project/ACL2/smtlink/z3_interface")
from ACL2_translator import to_smt, Q
s = to_smt()
X=s.isReal("X")
I=s.isReal("I")
J=s.isReal("J")
hypothesis=s.ifx(s.lt(0,X),s.ifx(s.lt(0,I),s.lt(0,J),False),False)
conclusion=s.lt(0,(lambda var0,var1:s.plus(var0,s.plus(s.nth(0,var1),s.nth(1,var1))))(X,s.array([I,J])))
s.prove(hypothesis, conclusion)

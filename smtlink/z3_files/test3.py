from sys import path
path.insert(0,"/ubc/cs/home/y/yanpeng/project/ACL2/smtlink/z3_interface")
from ACL2_translator import to_smt, Q
s = to_smt()
Y=s.isReal("Y")
=("")
hypothesis=s.lt(9,(lambda var0:s.times(2,(lambda var1:s.plus(var1,3))(var0)))(Y))
conclusion=False
s.prove(hypothesis, conclusion)

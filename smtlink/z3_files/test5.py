from sys import path
path.insert(0,"/ubc/cs/home/y/yanpeng/project/ACL2/smtlink/z3_interface")
from ACL2_translator import to_smt, Q
s = to_smt()
A=s.isReal("A")
hypothesis=s.notx(s.lt(A,10))
conclusion=s.notx(s.lt((lambda var0:s.ifx(False,1,s.times(var0,False)))(A),20))
s.prove(hypothesis, conclusion)

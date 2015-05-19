from sys import path
path.insert(0,"/ubc/cs/home/y/yanpeng/project/ACL2/smtlink/z3_interface")
from ACL22SMT import to_smt, Q
s = to_smt()
C=s.isReal("C")
A=s.isReal("A")
B=s.isReal("B")
hypothesis=s.ifx(s.lt(0,C),s.ifx(s.lt(C,1),s.ifx(s.lt(s.plus(A,B),0),s.lt(B,0),False),False),False)
conclusion=s.lt(s.plus(s.times(C,s.times(C,A)),s.times(C,B)),0)
s.prove(hypothesis, conclusion)

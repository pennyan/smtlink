from sys import path
path.insert(0,"/ubc/cs/home/y/yanpeng/project/ACL2/smtlink/z3_interface")
from ACL22SMT import to_smt, Q
s = to_smt()
A=s.isReal("A")
B=s.isReal("B")
hypothesis=True
conclusion=s.lt(s.times(2,s.times(A,B)),s.plus(s.times(A,A),s.times(B,B)))
s.prove(hypothesis, conclusion)

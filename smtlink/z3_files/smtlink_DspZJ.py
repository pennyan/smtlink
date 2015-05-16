from sys import path
path.insert(0,"/ubc/cs/home/y/yanpeng/project/ACL2/smtlink/z3_interface")
from ACL22SMT import to_smt, Q
s = to_smt()
X=s.isReal("X")
hypothesis=True
conclusion=s.equal(s.plus(X,X),s.times(1,(lambda var0:s.times(4,s.times(s.Q(1,2),var0)))(X)))
s.prove(hypothesis, conclusion)

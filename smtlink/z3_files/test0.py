from sys import path
path.insert(0,"/ubc/cs/home/y/yanpeng/project/ACL2/smtlink/z3_interface")
from ACL2_translator import to_smt, Q
s = to_smt()
X=s.isReal("X")
T=("T")
hypothesis=s.equal(s.plus(X,X),s.times(1,(lambda var0:s.times(2,var0))(X)))
conclusion=False
s.prove(hypothesis, conclusion)

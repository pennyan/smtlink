from sys import path
path.insert(0,"/ubc/cs/home/y/yanpeng/project/ACL2/smtlink/z3_interface")
from ACL2_translator import to_smt
s = to_smt()
CONST1=1
X=s.isReal("X")
Y=s.isReal("Y")
Z=s.isReal("Z")
hypothesis=s.ifx(s.notx(s.notx(s.lt(0,X))),s.ifx(s.equal(Z,s.plus(-4,2)),s.ifx(s.lt(Y,X),s.lt(Y,X),s.lt(s.plus(Y,1),X)),False),False)
conclusion=s.lt(s.multiply(X,Y),s.multiply(X,s.multiply(X,Z)))
s.prove(hypothesis, conclusion)

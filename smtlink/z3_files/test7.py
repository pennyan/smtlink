from sys import path
path.insert(0,"/ubc/cs/home/y/yanpeng/project/ACL2/smtlink/z3_interface")
from ACL2_translator import to_smt, Q
s = to_smt()
EXPT_PLUS_X_Y_SQUARE=s.isReal("EXPT_PLUS_X_Y_SQUARE")
X=s.isReal("X")
Y=s.isReal("Y")
hypothesis=s.ifx(s.notx(s.lt(EXPT_PLUS_X_Y_SQUARE,0)),True,False)
conclusion=s.lt(0,EXPT_PLUS_X_Y_SQUARE)
s.prove(hypothesis, conclusion)

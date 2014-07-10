from sys import path
path.insert(0,"/ubc/cs/home/y/yanpeng/project/ACL2/smtlink/z3_interface")
from ACL2_translator import to_smt, Q
s = to_smt()
EXPT_GAMMA_N=s.isReal("EXPT_GAMMA_N")
EXPT_GAMMA_M=s.isReal("EXPT_GAMMA_M")
A=s.isReal("A")
B=s.isReal("B")
GAMMA=s.isReal("GAMMA")
M=s.isReal("M")
N=s.isReal("N")
hypothesis=s.ifx(s.lt(0,EXPT_GAMMA_N),s.ifx(s.lt(0,EXPT_GAMMA_M),s.ifx(s.lt(EXPT_GAMMA_N,EXPT_GAMMA_M),s.ifx(s.lt(0,GAMMA),s.ifx(s.lt(GAMMA,1),s.ifx(s.lt(0,M),s.lt(M,N),False),False),False),False),False),False)
conclusion=s.notx(s.lt(False,False))
s.prove(hypothesis, conclusion)

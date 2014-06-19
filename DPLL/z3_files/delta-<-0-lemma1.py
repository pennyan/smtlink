from sys import path
path.insert(0,"/ubc/cs/home/y/yanpeng/project/ACL2/smtlink/z3_interface")
from ACL2_translator import to_smt, Q
s = to_smt()
EXPT_GAMMA_2N_MINUS_2=s.isReal("EXPT_GAMMA_2N_MINUS_2")
N=s.isReal("N")
hypothesis=s.ifx(s.lt(0,EXPT_GAMMA_2N_MINUS_2),s.notx(s.lt(N,4)),False)
conclusion=False
s.prove(hypothesis, conclusion)

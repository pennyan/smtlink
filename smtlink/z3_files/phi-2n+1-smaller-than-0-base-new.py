from sys import path
path.insert(0,"/ubc/cs/home/y/yanpeng/project/ACL2/smtlink/z3_interface")
from ACL22SMT import to_smt, Q
s = to_smt()
V0=s.isReal("V0")
hypothesis=False
conclusion=True
s.prove(hypothesis, conclusion)

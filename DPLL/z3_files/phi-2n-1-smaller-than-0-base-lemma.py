from sys import path
path.insert(0,"/ubc/cs/home/y/yanpeng/project/ACL2/smtlink/z3_interface")
from ACL2_translator import to_smt, Q
s = to_smt()
V0=s.isReal("V0")
PHI0=s.isReal("PHI0")
hypothesis=s.ifx(s.notx(s.lt(s.times(Q(10,9),V0),1)),s.ifx(s.notx(s.lt(Q(11,10),V0)),s.ifx(s.notx(s.lt(PHI0,0)),s.lt(PHI0,s.plus(-1,s.times(s.plus(1,V0),s.reciprocal(s.plus(Q(1599,1600),V0))))),False),False),False)
conclusion=s.lt(s.plus(s.times(Q(1,3125),PHI0),s.plus(s.times(s.plus(1,V0),s.reciprocal(s.plus(Q(3201,3200),V0))),s.plus(s.times(Q(1,125),s.times(s.plus(1,V0),s.reciprocal(s.plus(Q(1599,1600),V0)))),s.plus(s.times(Q(1,25),s.times(s.plus(1,V0),s.reciprocal(s.plus(Q(3199,3200),V0)))),s.times(Q(1,625),s.times(s.plus(1,V0),s.reciprocal(s.plus(Q(3197,3200),V0)))))))),Q(656,625))
s.prove(hypothesis, conclusion)

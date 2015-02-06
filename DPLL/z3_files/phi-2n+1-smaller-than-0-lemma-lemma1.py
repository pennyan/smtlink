from sys import path
path.insert(0,"/ubc/cs/home/y/yanpeng/project/ACL2/smtlink/z3_interface")
from ACL2_translator import to_smt, Q
s = to_smt()
I=s.isReal("I")
V0=s.isReal("V0")
DV=s.isReal("DV")
PHI0=s.isReal("PHI0")
hypothesis=s.ifx(s.notx(s.lt(s.plus(-1,I),3)),s.ifx(s.notx(s.lt(640,s.plus(-1,I))),s.ifx(s.notx(s.lt(s.times(Q(10,9),V0),1)),s.ifx(s.notx(s.lt(Q(11,10),V0)),s.ifx(s.notx(s.lt(1,s.negate(s.times(8000,DV)))),s.ifx(s.notx(s.lt(1,s.times(8000,DV))),s.ifx(s.notx(s.lt(PHI0,0)),s.lt(PHI0,s.plus(-1,s.times(s.plus(1,s.plus(DV,V0)),s.reciprocal(s.plus(Q(1601,1600),s.plus(V0,s.negate(s.times(Q(1,3200),I)))))))),False),False),False),False),False),False),False)
conclusion=s.lt(PHI0,s.plus(-1,s.times(s.plus(1,s.plus(DV,V0)),s.reciprocal(s.plus(Q(3201,3200),s.plus(V0,s.negate(s.times(Q(1,3200),I))))))))
s.prove(hypothesis, conclusion)

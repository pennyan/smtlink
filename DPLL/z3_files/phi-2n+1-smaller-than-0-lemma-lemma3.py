from sys import path
path.insert(0,"/ubc/cs/home/y/yanpeng/project/ACL2/smtlink/z3_interface")
from ACL2_translator import to_smt, Q
s = to_smt()
V0=s.isReal("V0")
DV=s.isReal("DV")
PHI0=s.isReal("PHI0")
hypothesis=s.ifx(s.lt(PHI0,s.plus(-1,s.plus(s.reciprocal(s.plus(Q(1599,1600),V0)),s.plus(s.times(DV,s.reciprocal(s.plus(Q(1599,1600),V0))),s.times(V0,s.reciprocal(s.plus(Q(1599,1600),V0))))))),s.ifx(s.notx(s.lt(s.plus(-5,s.plus(s.times(Q(1,5),PHI0),s.plus(s.reciprocal(s.plus(Q(1599,1600),V0)),s.plus(s.times(5,s.reciprocal(s.plus(Q(3199,3200),V0))),s.plus(s.times(DV,s.reciprocal(s.plus(Q(1599,1600),V0))),s.plus(s.times(V0,s.reciprocal(s.plus(Q(1599,1600),V0))),s.plus(s.times(5,s.times(DV,s.reciprocal(s.plus(Q(3199,3200),V0)))),s.times(5,s.times(V0,s.reciprocal(s.plus(Q(3199,3200),V0))))))))))),1)),s.ifx(s.notx(s.lt(s.times(Q(10,9),V0),1)),s.ifx(s.notx(s.lt(Q(11,10),V0)),s.ifx(s.notx(s.lt(1,s.negate(s.times(8000,DV)))),s.ifx(s.notx(s.lt(1,s.times(8000,DV))),s.notx(s.lt(PHI0,0)),False),False),False),False),False),False)
conclusion=s.lt(s.plus(-655,s.plus(s.times(Q(1,5),PHI0),s.plus(s.reciprocal(s.plus(Q(3197,3200),V0)),s.plus(s.times(5,s.reciprocal(s.plus(Q(1599,1600),V0))),s.plus(s.times(25,s.reciprocal(s.plus(Q(3199,3200),V0))),s.plus(s.times(625,s.reciprocal(s.plus(Q(3201,3200),V0))),s.plus(s.times(DV,s.reciprocal(s.plus(Q(3197,3200),V0))),s.plus(s.times(V0,s.reciprocal(s.plus(Q(3197,3200),V0))),s.plus(s.times(5,s.times(DV,s.reciprocal(s.plus(Q(1599,1600),V0)))),s.plus(s.times(5,s.times(V0,s.reciprocal(s.plus(Q(1599,1600),V0)))),s.plus(s.times(25,s.times(DV,s.reciprocal(s.plus(Q(3199,3200),V0)))),s.plus(s.times(25,s.times(V0,s.reciprocal(s.plus(Q(3199,3200),V0)))),s.plus(s.times(625,s.times(DV,s.reciprocal(s.plus(Q(3201,3200),V0)))),s.times(625,s.times(V0,s.reciprocal(s.plus(Q(3201,3200),V0))))))))))))))))),1)
s.prove(hypothesis, conclusion)

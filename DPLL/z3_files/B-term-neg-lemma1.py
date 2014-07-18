from sys import path
path.insert(0,"/ubc/cs/home/y/yanpeng/project/ACL2/smtlink/z3_interface")
from ACL2_translator import to_smt, Q
s = to_smt()
EXPT_GAMMA_MINUS_H=s.isReal("EXPT_GAMMA_MINUS_H")
EXPT_GAMMA_H=s.isReal("EXPT_GAMMA_H")
H=s.isReal("H")
G1=s.isReal("G1")
V0=s.isReal("V0")
DV=s.isReal("DV")
hypothesis=s.ifx(s.equal(EXPT_GAMMA_MINUS_H,s.reciprocal(EXPT_GAMMA_H)),s.ifx(s.lt(1,EXPT_GAMMA_H),s.ifx(s.notx(s.lt(H,1)),s.ifx(s.equal(G1,Q(1,3200)),s.ifx(s.notx(s.lt(V0,Q(9,10))),s.ifx(s.notx(s.lt(Q(11,10),V0)),s.ifx(s.notx(s.lt(DV,s.negate(s.times(2,Q(-1,16000))))),s.notx(s.lt(s.times(2,Q(-1,16000)),DV)),False),False),False),False),False),False),False)
conclusion=s.lt(s.plus(s.times(EXPT_GAMMA_H,(lambda var0,var1,var2,var3:s.plus(-1,s.times(s.times(1,s.reciprocal(s.times(1,1))),s.times(s.plus(1,s.times(1,s.plus(var1,var2))),s.reciprocal(s.plus(1,s.times(1,s.plus(s.times(var0,var3),1))))))))(H,V0,DV,G1)),s.times(EXPT_GAMMA_MINUS_H,(lambda var4,var5,var6,var7:s.plus(-1,s.times(s.times(1,s.reciprocal(s.times(1,1))),s.times(s.plus(1,s.times(1,s.plus(var5,var6))),s.reciprocal(s.plus(1,s.times(1,s.plus(s.times(var4,var7),1))))))))(s.negate(H),V0,DV,G1))),0)
s.prove(hypothesis, conclusion)

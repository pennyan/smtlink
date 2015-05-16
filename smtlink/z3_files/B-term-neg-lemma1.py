from sys import path
path.insert(0,"/ubc/cs/home/y/yanpeng/project/ACL2/smtlink/z3_interface")
from ACL22SMT import to_smt, Q
s = to_smt()
EXPT_GAMMA_MINUS_H=s.isReal("EXPT_GAMMA_MINUS_H")
EXPT_GAMMA_H=s.isReal("EXPT_GAMMA_H")
H=s.isReal("H")
G1=s.isReal("G1")
V0=s.isReal("V0")
DV=s.isReal("DV")
hypothesis=s.ifx(s.equal(s.times(EXPT_GAMMA_MINUS_H,EXPT_GAMMA_H),1),s.ifx(s.lt(0,EXPT_GAMMA_MINUS_H),s.ifx(s.notx(s.lt(s.times(1,s.reciprocal(5)),EXPT_GAMMA_MINUS_H)),s.ifx(s.notx(s.lt(H,1)),s.ifx(s.notx(s.lt(640,H)),s.ifx(s.equal(G1,s.Qx(1,3200)),s.ifx(s.notx(s.lt(V0,s.Qx(9,10))),s.ifx(s.notx(s.lt(s.Qx(11,10),V0)),s.ifx(s.notx(s.lt(DV,s.negate(s.times(-2,s.Qx(-1,16000))))),s.notx(s.lt(s.times(-2,s.Qx(-1,16000)),DV)),False),False),False),False),False),False),False),False),False)
conclusion=s.lt(s.plus(s.times(EXPT_GAMMA_H,(lambda var0,var1,var2,var3:s.plus(-1,s.times(s.times(1,s.reciprocal(s.times(1,1))),s.times(s.plus(1,s.times(1,s.plus(var1,var2))),s.reciprocal(s.plus(1,s.times(1,s.plus(s.times(var0,var3),(lambda var4:s.plus(s.times(1,s.times(s.plus(1,s.times(1,var4)),s.reciprocal(s.times(1,s.times(1,1))))),s.negate(s.reciprocal(1))))(var1)))))))))(H,V0,DV,G1)),s.times(EXPT_GAMMA_MINUS_H,(lambda var5,var6,var7,var8:s.plus(-1,s.times(s.times(1,s.reciprocal(s.times(1,1))),s.times(s.plus(1,s.times(1,s.plus(var6,var7))),s.reciprocal(s.plus(1,s.times(1,s.plus(s.times(var5,var8),(lambda var9:s.plus(s.times(1,s.times(s.plus(1,s.times(1,var9)),s.reciprocal(s.times(1,s.times(1,1))))),s.negate(s.reciprocal(1))))(var6)))))))))(s.negate(H),V0,DV,G1))),0)
s.prove(hypothesis, conclusion)

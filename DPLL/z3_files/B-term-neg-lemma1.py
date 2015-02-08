from sys import path
path.insert(0,"/ubc/cs/home/y/yanpeng/project/ACL2/smtlink/z3_interface")
from ACL2_translator import to_smt, Q
s = to_smt()
EXPT_GAMMA_MINUS_H=s.isReal("EXPT_GAMMA_MINUS_H")
EXPT_GAMMA_H=s.isReal("EXPT_GAMMA_H")
H=s.isReal("H")
DC=s.isReal("DC")
G1=s.isReal("G1")
V0=s.isReal("V0")
DV=s.isReal("DV")
hypothesis=s.ifx(s.equal(s.times(EXPT_GAMMA_MINUS_H,EXPT_GAMMA_H),1),s.ifx(s.lt(0,EXPT_GAMMA_MINUS_H),s.ifx(s.notx(s.lt(s.times(1,s.reciprocal(5)),EXPT_GAMMA_MINUS_H)),s.ifx(s.notx(s.lt(H,1)),s.ifx(s.notx(s.lt(640,H)),s.ifx(s.notx(s.lt(DC,0)),s.ifx(s.lt(DC,1),s.ifx(s.equal(G1,Q(1,3200)),s.ifx(s.notx(s.lt(V0,Q(9,10))),s.ifx(s.notx(s.lt(Q(11,10),V0)),s.ifx(s.notx(s.lt(DV,s.negate(s.times(-2,Q(-1,16000))))),s.notx(s.lt(s.times(-2,Q(-1,16000)),DV)),False),False),False),False),False),False),False),False),False),False),False)
conclusion=s.lt(s.plus(s.times(EXPT_GAMMA_H,(lambda var0,var1,var2,var3,var4:s.plus(-1,s.times(s.times(1,s.reciprocal(s.times(1,1))),s.times(s.plus(1,s.times(1,s.plus(var1,var2))),s.reciprocal(s.plus(1,s.times(1,s.plus(s.times(s.plus(var0,var4),var3),(lambda var5:s.plus(s.times(1,s.times(s.plus(1,s.times(1,var5)),s.reciprocal(s.times(1,s.times(1,1))))),s.negate(s.reciprocal(1))))(var1)))))))))(H,V0,DV,G1,DC)),s.times(EXPT_GAMMA_MINUS_H,(lambda var6,var7,var8,var9,var10:s.plus(-1,s.times(s.times(1,s.reciprocal(s.times(1,1))),s.times(s.plus(1,s.times(1,s.plus(var7,var8))),s.reciprocal(s.plus(1,s.times(1,s.plus(s.times(s.plus(var6,var10),var9),(lambda var11:s.plus(s.times(1,s.times(s.plus(1,s.times(1,var11)),s.reciprocal(s.times(1,s.times(1,1))))),s.negate(s.reciprocal(1))))(var7)))))))))(s.negate(H),V0,DV,G1,DC))),0)
s.prove(hypothesis, conclusion)

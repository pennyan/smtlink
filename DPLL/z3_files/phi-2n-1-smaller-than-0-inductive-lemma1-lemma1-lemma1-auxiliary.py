from sys import path
path.insert(0,"/ubc/cs/home/y/yanpeng/project/ACL2/smtlink/z3_interface")
from ACL2_translator import to_smt, Q
s = to_smt()
N_MINUS_2=s.isReal("N_MINUS_2")
G1=s.isReal("G1")
V0=s.isReal("V0")
DV=s.isReal("DV")
PHI0=s.isReal("PHI0")
hypothesis=s.ifx(s.notx(s.lt(N_MINUS_2,2)),s.ifx(s.equal(G1,Q(1,3200)),s.ifx(s.notx(s.lt(V0,Q(9,10))),s.ifx(s.notx(s.lt(Q(11,10),V0)),s.ifx(s.notx(s.lt(DV,s.negate(s.times(-2,Q(-1,16000))))),s.ifx(s.notx(s.lt(s.times(-2,Q(-1,16000)),DV)),s.ifx(s.notx(s.lt(PHI0,0)),s.lt(PHI0,s.plus(-1,(lambda var0,var1,var2,var3:s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,s.plus(var1,var2)))),s.reciprocal(s.plus(1,s.times(1,s.times(var0,var3))))))(s.plus(1,(lambda var4,var5,var6:s.plus(s.times((lambda var7:s.plus(s.times(1,s.times(s.plus(1,s.times(1,var7)),s.reciprocal(s.times(1,s.times(1,1))))),s.negate(s.reciprocal(1))))(var5),s.reciprocal(var6)),s.negate(var4)))(s.plus(N_MINUS_2,2),V0,G1)),V0,DV,G1))),False),False),False),False),False),False),False)
conclusion=s.ifx(s.lt(0,s.plus(-1,(lambda var8,var9,var10,var11:s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,s.plus(var9,var10)))),s.reciprocal(s.plus(1,s.times(1,s.times(var8,var11))))))(s.plus(1,(lambda var12,var13,var14:s.plus(s.times((lambda var15:s.plus(s.times(1,s.times(s.plus(1,s.times(1,var15)),s.reciprocal(s.times(1,s.times(1,1))))),s.negate(s.reciprocal(1))))(var13),s.reciprocal(var14)),s.negate(var12)))(s.plus(N_MINUS_2,2),V0,G1)),V0,DV,G1))),s.lt(0,s.plus(-1,(lambda var16,var17,var18,var19:s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,s.plus(var17,var18)))),s.reciprocal(s.plus(1,s.times(1,s.times(var16,var19))))))(s.plus(1,(lambda var20,var21,var22:s.plus(s.times((lambda var23:s.plus(s.times(1,s.times(s.plus(1,s.times(1,var23)),s.reciprocal(s.times(1,s.times(1,1))))),s.negate(s.reciprocal(1))))(var21),s.reciprocal(var22)),s.negate(var20)))(s.plus(-1,s.plus(N_MINUS_2,2)),V0,G1)),V0,DV,G1))),False)
s.prove(hypothesis, conclusion)

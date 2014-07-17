from sys import path
path.insert(0,"/ubc/cs/home/y/yanpeng/project/ACL2/smtlink/z3_interface")
from ACL2_translator import to_smt, Q
s = to_smt()
N_MINUS_2=s.isReal("N_MINUS_2")
G1=s.isReal("G1")
V0=s.isReal("V0")
DV=s.isReal("DV")
PHI0=s.isReal("PHI0")
hypothesis=s.ifx(s.notx(s.lt(N_MINUS_2,2)),s.ifx(s.equal(G1,Q(1,3200)),s.ifx(s.notx(s.lt(V0,Q(9,10))),s.ifx(s.notx(s.lt(Q(11,10),V0)),s.ifx(s.notx(s.lt(DV,s.negate(s.times(2,Q(-1,16000))))),s.ifx(s.notx(s.lt(s.times(2,Q(-1,16000)),DV)),s.ifx(s.notx(s.lt(PHI0,0)),s.lt(PHI0,s.plus(-1,(lambda var0,var1,var2,var3:s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,s.plus(var1,var2)))),s.reciprocal(s.plus(1,s.times(1,s.times(var0,var3))))))(s.plus(1,(lambda var4,var5:s.plus(s.times(1,s.reciprocal(var5)),s.negate(var4)))(s.plus(s.floor(N_MINUS_2),2),G1)),V0,DV,G1))),False),False),False),False),False),False),False)
conclusion=s.ifx(s.lt(PHI0,s.plus(-1,(lambda var6,var7,var8,var9:s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,s.plus(var7,var8)))),s.reciprocal(s.plus(1,s.times(1,s.times(var6,var9))))))(s.plus(1,(lambda var10,var11:s.plus(s.times(1,s.reciprocal(var11)),s.negate(var10)))(s.plus(-1,s.plus(s.floor(N_MINUS_2),2)),G1)),V0,DV,G1))),s.ifx(s.lt(0,s.plus(-1,(lambda var12,var13,var14,var15:s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,s.plus(var13,var14)))),s.reciprocal(s.plus(1,s.times(1,s.times(var12,var15))))))(s.plus(1,(lambda var16,var17:s.plus(s.times(1,s.reciprocal(var17)),s.negate(var16)))(s.plus(s.floor(N_MINUS_2),2),G1)),V0,DV,G1))),s.lt(0,s.plus(-1,(lambda var18,var19,var20,var21:s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,s.plus(var19,var20)))),s.reciprocal(s.plus(1,s.times(1,s.times(var18,var21))))))(s.plus(1,(lambda var22,var23:s.plus(s.times(1,s.reciprocal(var23)),s.negate(var22)))(s.plus(-1,s.plus(s.floor(N_MINUS_2),2)),G1)),V0,DV,G1))),False),False)
s.prove(hypothesis, conclusion)

from sys import path
path.insert(0,"../smtlink/z3_interface")
from RewriteExpt import to_smt_w_expt
s = to_smt_w_expt()
H=s.isReal("H")
V0=s.isReal("V0")
DV=s.isReal("DV")
G1=s.isReal("G1")
GAMMA=s.isReal("GAMMA")
hypothesis=s.ifx(s.notx(s.lt(H,1)),s.ifx(s.lt(0,V0),s.ifx(s.lt(0,DV),s.ifx(s.lt(0,G1),s.ifx(s.lt(s.reciprocal(10),GAMMA),s.ifx(s.lt(G1,s.reciprocal(8)),s.ifx(s.lt(DV,s.times(s.reciprocal(4),s.times(s.times(1,s.reciprocal(1)),G1))),s.ifx(s.lt(H,s.reciprocal(s.times(2,G1))),s.lt(GAMMA,s.reciprocal(2)),False),False),False),False),False),False),False),False)
conclusion=s.lt((lambda var0,var1,var2,var3,var4:s.times((lambda var5,var6:s.expt(var5,s.negate(var6)))(var4,var0),(lambda var7,var8,var9,var10:s.plus(-1,s.times(s.times(1,s.reciprocal(s.times(1,1))),s.times(s.plus(1,s.times(1,s.plus(var8,var9))),s.reciprocal(s.plus(1,s.times(1,s.plus(s.times(var7,var10),(lambda var11:s.plus(s.times(1,s.times(s.plus(1,s.times(1,var11)),s.reciprocal(s.times(1,s.times(1,1))))),s.negate(s.reciprocal(1))))(var8)))))))))(var0,var1,var2,var3)))(s.negate(H),V0,DV,G1,GAMMA),s.negate((lambda var12,var13,var14,var15,var16:s.times((lambda var17,var18:s.expt(var17,s.negate(var18)))(var16,var12),(lambda var19,var20,var21,var22:s.plus(-1,s.times(s.times(1,s.reciprocal(s.times(1,1))),s.times(s.plus(1,s.times(1,s.plus(var20,var21))),s.reciprocal(s.plus(1,s.times(1,s.plus(s.times(var19,var22),(lambda var23:s.plus(s.times(1,s.times(s.plus(1,s.times(1,var23)),s.reciprocal(s.times(1,s.times(1,1))))),s.negate(s.reciprocal(1))))(var20)))))))))(var12,var13,var14,var15)))(H,V0,DV,G1,GAMMA)))
s.prove(hypothesis, conclusion)

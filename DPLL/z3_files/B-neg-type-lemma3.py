from sys import path
path.insert(0,"/ubc/cs/home/y/yanpeng/project/ACL2/smtlink/z3_interface")
from ACL2_translator import to_smt, Q
s = to_smt()
var23=s.isReal("var23")
N-MINUS-2=s.isReal("N-MINUS-2")
hypothesis=s.ifx(s.rationalp(V0),s.ifx(s.rationalp(G1),s.rationalp(DV),False),False)
conclusion=s.rationalp((lambda var0,var1,var2,var3,var4:s.ifx(s.ifx(s.notx(s.integerp(var1)),s.notx(s.integerp(var1)),s.ifx(s.notx(s.integerp(var0)),s.notx(s.integerp(var0)),s.lt(var1,var0))),0,s.plus((lambda var5,var6,var7,var8:s.times((lambda var9:False)(var5),(lambda var10,var11,var12,var13:s.plus(-1,s.times(s.times(1,s.reciprocal(s.times(1,1))),s.times(s.plus(1,s.times(1,s.plus(var11,var12))),s.reciprocal(s.plus(1,s.times(1,s.plus(s.times(var10,var13),1))))))))(var5,var6,var7,var8)))(var1,var2,var3,var4),s.plus((lambda var14,var15,var16,var17:s.times((lambda var18:False)(var14),(lambda var19,var20,var21,var22:s.plus(-1,s.times(s.times(1,s.reciprocal(s.times(1,1))),s.times(s.plus(1,s.times(1,s.plus(var20,var21))),s.reciprocal(s.plus(1,s.times(1,s.plus(s.times(var19,var22),1))))))))(var14,var15,var16,var17)))(s.negate(var1),var2,var3,var4),var23))))(1,s.floor(N-MINUS-2),V0,DV,G1))
s.prove(hypothesis, conclusion)

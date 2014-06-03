from sys import path
path.insert(0,"/ubc/cs/home/y/yanpeng/project/ACL2/smtlink/z3_interface")
from ACL2_translator import to_smt, Q
s = to_smt()
A=s.isReal("A")
B=s.isReal("B")
hypothesis=True
conclusion=s.notx(s.lt((lambda var0,var1:(lambda var2,var3:s.plus(var2,var3))(var0,(lambda var4:s.negate(var4))(var1)))((lambda var5:(lambda var6,var7:s.times(var6,var7))(var5,var5))((lambda var8,var9:s.plus(var8,var9))(A,B)),(lambda var10,var11:s.times(var10,var11))((lambda var12:(lambda var13,var14:s.times(var13,var14))(2,var12))(A),B)),(lambda var15,var16:s.times(var15,var16))((lambda var17:(lambda var18,var19:s.times(var18,var19))(2,var17))(A),B)))
s.prove(hypothesis, conclusion)

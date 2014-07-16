from sys import path
path.insert(0,"/ubc/cs/home/y/yanpeng/project/ACL2/smtlink/z3_interface")
from ACL2_translator import to_smt, Q
s = to_smt()
EXPT_GAMMA_N=s.isReal("EXPT_GAMMA_N")
EXPT_GAMMA_M=s.isReal("EXPT_GAMMA_M")
A=s.isReal("A")
B=s.isReal("B")
GAMMA=s.isReal("GAMMA")
M=s.isReal("M")
N=s.isReal("N")
hypothesis=s.ifx(s.lt(0,EXPT_GAMMA_N),s.ifx(s.lt(0,EXPT_GAMMA_M),s.ifx(s.lt(EXPT_GAMMA_N,EXPT_GAMMA_M),s.ifx(s.lt(0,GAMMA),s.ifx(s.lt(GAMMA,1),s.ifx(s.lt(0,M),s.lt(M,N),False),False),False),False),False),False)
conclusion=s.notx(s.lt((lambda var0,var1:s.times(var0,var1))(EXPT_GAMMA_M,(lambda var2,var3:(lambda var4,var5:s.plus(var4,var5))(var2,(lambda var6:s.negate(var6))(var3)))((lambda var7:(lambda var8,var9:s.times(var8,var9))(var7,var7))((lambda var10,var11:s.plus(var10,var11))(A,B)),(lambda var12,var13:s.times(var12,var13))((lambda var14:(lambda var15,var16:s.times(var15,var16))(2,var14))(A),B))),(lambda var17,var18:s.times(var17,var18))(EXPT_GAMMA_N,(lambda var21,var22:s.times(var21,var22))((lambda var23:(lambda var24,var25:s.times(var24,var25))(2,var23))(A),B))))
s.prove(hypothesis, conclusion)

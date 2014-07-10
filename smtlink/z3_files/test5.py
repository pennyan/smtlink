from sys import path
path.insert(0,"/ubc/cs/home/y/yanpeng/project/ACL2/smtlink/z3_interface")
from ACL2_translator import to_smt, Q
s = to_smt()
var6=s.isReal("var6")
A=s.isReal("A")
hypothesis=s.notx(s.lt(A,10))
conclusion=s.notx(s.lt((lambda var0,var6:s.ifx((lambda var1:s.ifx(s.integerp(var1),s.notx(s.lt(0,var1)),True))(var0),1,s.times(var0,(lambda var2,var6:s.ifx((lambda var3:s.ifx(s.integerp(var3),s.notx(s.lt(0,var3)),True))(var2),1,s.times(var2,(lambda var4,var6:s.ifx((lambda var5:s.ifx(s.integerp(var5),s.notx(s.lt(0,var5)),True))(var4),1,s.times(var4,var6)))(s.plus(-1,var2),var6))))(s.plus(-1,var0),var6))))(A,var6),20))
s.prove(hypothesis, conclusion)

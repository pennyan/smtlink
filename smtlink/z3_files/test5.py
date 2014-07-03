from sys import path
path.insert(0,"/ubc/cs/home/y/yanpeng/project/ACL2/smtlink/z3_interface")
from ACL2_translator import to_smt, Q
s = to_smt()
var3=s.isReal("var3")
hypothesis=s.notx(s.lt(A,10))
conclusion=s.notx(s.lt((lambda var0:s.ifx(False,1,s.times(var0,(lambda var1:s.ifx(False,1,s.times(var1,(lambda var2:s.ifx(False,1,s.times(var2,var3)))(s.plus(-1,var1)))))(s.plus(-1,var0)))))(A),20))
s.prove(hypothesis, conclusion)

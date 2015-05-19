from sys import path
path.insert(0,"/ubc/cs/home/y/yanpeng/project/ACL2/smtlink/z3_interface")
from ACL22SMT import to_smt, Q
s = to_smt()
var4=s.isReal("var4")
N=s.isReal("N")
hypothesis=s.notx(s.lt(2,N))
conclusion=s.lt((lambda var0:s.ifx(False,1,s.times(var0,(lambda var1:s.ifx(False,1,s.times(var1,(lambda var2:s.ifx(False,1,s.times(var2,(lambda var3:s.ifx(False,1,s.times(var3,var4)))(s.plus(-1,var2)))))(s.plus(-1,var1)))))(s.plus(-1,var0)))))(N),10)
s.prove(hypothesis, conclusion)

from sys import path
path.insert(0,"/ubc/cs/home/y/yanpeng/project/ACL2/smtlink/z3_interface")
from ACL22SMT import to_smt, Q
s = to_smt()
var1=s.isInt("var1")
N=s.isInt("N")
hypothesis=s.notx(s.lt(2,N))
conclusion=s.lt((lambda var0:s.ifx(s.ifx(s.notx(s.lt(0,var0)),s.notx(s.lt(0,var0)),s.notx(s.integerp(var0))),1,s.times(var0,var1)))(N),10)
s.prove(hypothesis, conclusion)

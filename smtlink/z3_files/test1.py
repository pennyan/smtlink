from sys import path
path.insert(0,"/ubc/cs/home/y/yanpeng/project/ACL2/smtlink/z3_interface")
from ACL2_translator import to_smt, Q
s = to_smt()
=("")
=("")
=("")
=("")
=("")
hypothesis=s.lt((lambda var0,var1:s.times(var0,s.plus(1,var1)))(X,Y),(lambda var2,var3:s.times(var2,s.plus(1,var3)))(X,(lambda var4,var5:s.times(var4,s.plus(1,var5)))(X,Z)))
conclusion=False
s.prove(hypothesis, conclusion)

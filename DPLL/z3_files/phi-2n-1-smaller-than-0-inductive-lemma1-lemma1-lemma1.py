from sys import path
path.insert(0,"/ubc/cs/home/y/yanpeng/project/ACL2/smtlink/z3_interface")
from ACL2_translator import to_smt, Q
s = to_smt()
N_MINUS_2=s.isReal("N_MINUS_2")
PHI0=s.isReal("PHI0")
hypothesis=s.ifx(s.notx(s.lt(s.plus(-1,N_MINUS_2),1)),s.ifx(s.notx(s.lt(PHI0,0)),s.lt(PHI0,s.plus(-1,(lambda var0:s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,1))),s.reciprocal(s.plus(1,s.times(1,s.times(var0,Q(1,3200)))))))(s.plus(1,(lambda var1:s.plus(s.times(s.plus(s.times(s.times(1,s.reciprocal(s.times(1,s.times(1,1)))),s.plus(1,s.times(1,1))),s.negate(s.times(1,s.reciprocal(1)))),s.reciprocal(Q(1,3200))),s.negate(var1)))(s.plus(N_MINUS_2,2)))))),False),False)
conclusion=s.lt(PHI0,s.plus(-1,(lambda var2:s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,1))),s.reciprocal(s.plus(1,s.times(1,s.times(var2,Q(1,3200)))))))(s.plus(1,(lambda var3:s.plus(s.times(s.plus(s.times(s.times(1,s.reciprocal(s.times(1,s.times(1,1)))),s.plus(1,s.times(1,1))),s.negate(s.times(1,s.reciprocal(1)))),s.reciprocal(Q(1,3200))),s.negate(var3)))(s.plus(-1,s.plus(N_MINUS_2,2)))))))
s.prove(hypothesis, conclusion)

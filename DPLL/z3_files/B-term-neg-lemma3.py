from sys import path
path.insert(0,"/ubc/cs/home/y/yanpeng/project/ACL2/smtlink/z3_interface")
from ACL2_translator import to_smt, Q
s = to_smt()
EXPT_GAMMA_MINUS_H=s.isReal("EXPT_GAMMA_MINUS_H")
EXPT_GAMMA_H=s.isReal("EXPT_GAMMA_H")
H=s.isReal("H")
hypothesis=s.ifx(s.equal(EXPT_GAMMA_MINUS_H,s.reciprocal(EXPT_GAMMA_H)),s.ifx(s.lt(1,EXPT_GAMMA_H),s.notx(s.lt(H,1)),False),False)
conclusion=s.lt(s.plus(s.times(EXPT_GAMMA_H,(lambda var0:s.plus(-1,s.times(s.times(1,s.reciprocal(s.times(1,1))),s.times(s.plus(1,s.times(1,1)),s.reciprocal(s.plus(1,s.times(1,s.plus(s.times(var0,Q(1,3200)),s.plus(s.times(s.times(1,s.reciprocal(s.times(1,s.times(1,1)))),s.plus(1,s.times(1,1))),s.negate(s.times(1,s.reciprocal(1))))))))))))(H)),s.times(EXPT_GAMMA_MINUS_H,(lambda var1:s.plus(-1,s.times(s.times(1,s.reciprocal(s.times(1,1))),s.times(s.plus(1,s.times(1,1)),s.reciprocal(s.plus(1,s.times(1,s.plus(s.times(var1,Q(1,3200)),s.plus(s.times(s.times(1,s.reciprocal(s.times(1,s.times(1,1)))),s.plus(1,s.times(1,1))),s.negate(s.times(1,s.reciprocal(1))))))))))))(s.negate(H)))),0)
s.prove(hypothesis, conclusion)

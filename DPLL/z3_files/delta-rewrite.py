from sys import path
path.insert(0,"/ubc/cs/home/y/yanpeng/project/ACL2/smtlink/z3_interface")
from ACL2_translator import to_smt, Q
s = to_smt()
EXPT_GAMMA_1_MINUS_N=s.isReal("EXPT_GAMMA_1_MINUS_N")
EXPT_GAMMA_N_MINUS_1=s.isReal("EXPT_GAMMA_N_MINUS_1")
EXPT_GAMMA_2N_MINUS_1=s.isReal("EXPT_GAMMA_2N_MINUS_1")
EXPT_GAMMA_2N=s.isReal("EXPT_GAMMA_2N")
N=s.isReal("N")
hypothesis=s.notx(s.lt(N,4))
conclusion=s.equal((lambda var0:s.plus(s.plus(s.times(False,s.plus(-1,(lambda var1:s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,1))),s.reciprocal(s.plus(1,s.times(1,s.times(var1,Q(1,3200)))))))(s.plus(-1,(lambda var2:s.plus(s.times(s.plus(s.times(s.times(1,s.reciprocal(s.times(1,s.times(1,1)))),s.plus(1,s.times(1,1))),s.negate(s.times(1,s.reciprocal(1)))),s.reciprocal(Q(1,3200))),s.negate(var2)))(var0))))),s.negate(s.times(False,s.plus(-1,(lambda var3:s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,1))),s.reciprocal(s.plus(1,s.times(1,s.times(var3,Q(1,3200)))))))((lambda var4:s.plus(s.times(s.plus(s.times(s.times(1,s.reciprocal(s.times(1,s.times(1,1)))),s.plus(1,s.times(1,1))),s.negate(s.times(1,s.reciprocal(1)))),s.reciprocal(Q(1,3200))),s.negate(var4)))(var0)))))),s.plus(s.plus(s.times(False,s.plus(-1,(lambda var5:s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,1))),s.reciprocal(s.plus(1,s.times(1,s.times(var5,Q(1,3200)))))))((lambda var6:s.plus(s.times(s.plus(s.times(s.times(1,s.reciprocal(s.times(1,s.times(1,1)))),s.plus(1,s.times(1,1))),s.negate(s.times(1,s.reciprocal(1)))),s.reciprocal(Q(1,3200))),s.negate(var6)))(var0)))),s.negate(s.times(False,s.plus(-1,(lambda var7:s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,1))),s.reciprocal(s.plus(1,s.times(1,s.times(var7,Q(1,3200)))))))(s.plus(1,(lambda var8:s.plus(s.times(s.plus(s.times(s.times(1,s.reciprocal(s.times(1,s.times(1,1)))),s.plus(1,s.times(1,1))),s.negate(s.times(1,s.reciprocal(1)))),s.reciprocal(Q(1,3200))),s.negate(var8)))(var0))))))),s.times(False,s.plus(s.times(False,s.plus(-1,s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,1))),s.reciprocal(s.plus(1,s.times(1,s.plus(s.times(Q(1,3200),s.plus(-1,var0)),s.plus(s.times(s.times(1,s.reciprocal(s.times(1,s.times(1,1)))),s.plus(1,s.times(1,1))),s.negate(s.times(1,s.reciprocal(1))))))))))),s.times(False,s.plus(-1,s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,1))),s.reciprocal(s.plus(1,s.times(1,s.plus(s.times(Q(1,3200),s.plus(1,s.negate(var0))),s.plus(s.times(s.times(1,s.reciprocal(s.times(1,s.times(1,1)))),s.plus(1,s.times(1,1))),s.negate(s.times(1,s.reciprocal(1))))))))))))))))(N),(lambda var9:s.plus(s.times(False,s.plus((lambda var10:s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,1))),s.reciprocal(s.plus(1,s.times(1,s.times(var10,Q(1,3200)))))))(s.plus(-1,(lambda var11:s.plus(s.times(s.plus(s.times(s.times(1,s.reciprocal(s.times(1,s.times(1,1)))),s.plus(1,s.times(1,1))),s.negate(s.times(1,s.reciprocal(1)))),s.reciprocal(Q(1,3200))),s.negate(var11)))(var9))),s.negate((lambda var12:s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,1))),s.reciprocal(s.plus(1,s.times(1,s.times(var12,Q(1,3200)))))))((lambda var13:s.plus(s.times(s.plus(s.times(s.times(1,s.reciprocal(s.times(1,s.times(1,1)))),s.plus(1,s.times(1,1))),s.negate(s.times(1,s.reciprocal(1)))),s.reciprocal(Q(1,3200))),s.negate(var13)))(var9))))),s.plus(s.times(False,s.plus((lambda var14:s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,1))),s.reciprocal(s.plus(1,s.times(1,s.times(var14,Q(1,3200)))))))((lambda var15:s.plus(s.times(s.plus(s.times(s.times(1,s.reciprocal(s.times(1,s.times(1,1)))),s.plus(1,s.times(1,1))),s.negate(s.times(1,s.reciprocal(1)))),s.reciprocal(Q(1,3200))),s.negate(var15)))(var9)),s.negate((lambda var16:s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,1))),s.reciprocal(s.plus(1,s.times(1,s.times(var16,Q(1,3200)))))))(s.plus(1,(lambda var17:s.plus(s.times(s.plus(s.times(s.times(1,s.reciprocal(s.times(1,s.times(1,1)))),s.plus(1,s.times(1,1))),s.negate(s.times(1,s.reciprocal(1)))),s.reciprocal(Q(1,3200))),s.negate(var17)))(var9)))))),s.plus(s.times(s.times(False,False),s.plus(-1,s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,1))),s.reciprocal(s.plus(1,s.times(1,s.plus(s.times(Q(1,3200),s.plus(-1,var9)),s.plus(s.times(s.times(1,s.reciprocal(s.times(1,s.times(1,1)))),s.plus(1,s.times(1,1))),s.negate(s.times(1,s.reciprocal(1))))))))))),s.times(s.times(False,False),s.plus(-1,s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,1))),s.reciprocal(s.plus(1,s.times(1,s.plus(s.times(Q(1,3200),s.plus(1,s.negate(var9))),s.plus(s.times(s.times(1,s.reciprocal(s.times(1,s.times(1,1)))),s.plus(1,s.times(1,1))),s.negate(s.times(1,s.reciprocal(1)))))))))))))))(N))
s.prove(hypothesis, conclusion)

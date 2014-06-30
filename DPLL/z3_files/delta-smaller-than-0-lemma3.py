from sys import path
path.insert(0,"/ubc/cs/home/y/yanpeng/project/ACL2/smtlink/z3_interface")
from ACL2_translator import to_smt, Q
s = to_smt()
EXPT_GAMMA_2_MINUS_2N=s.isReal("EXPT_GAMMA_2_MINUS_2N")
EXPT_GAMMA_1=s.isReal("EXPT_GAMMA_1")
EXPT_GAMMA_2=s.isReal("EXPT_GAMMA_2")
EXPT_GAMMA_2N_MINUS_2=s.isReal("EXPT_GAMMA_2N_MINUS_2")
EXPT_GAMMA_2N_MINUS_1=s.isReal("EXPT_GAMMA_2N_MINUS_1")
EXPT_GAMMA_2N=s.isReal("EXPT_GAMMA_2N")
N=s.isReal("N")
V0=s.isReal("V0")
G1=s.isReal("G1")
hypothesis=s.ifx(s.lt(s.times(2,N),EXPT_GAMMA_2_MINUS_2N),s.ifx(s.notx(s.lt(N,3)),s.ifx(s.notx(s.lt(V0,Q(9,10))),s.ifx(s.notx(s.lt(Q(11,10),V0)),s.equal(G1,Q(1,3200)),False),False),False),False)
conclusion=s.implies(s.lt(s.times(s.plus(s.times(EXPT_GAMMA_2,s.plus((lambda var0,var1,var2:s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,var1))),s.reciprocal(s.plus(1,s.times(1,s.times(var0,var2))))))(s.plus(-1,(lambda var3,var4,var5:s.plus(s.times((lambda var6:s.plus(s.times(s.times(1,s.reciprocal(s.times(1,s.times(1,1)))),s.plus(1,s.times(1,var6))),s.negate(s.times(1,s.reciprocal(1)))))(var4),s.reciprocal(var5)),s.negate(var3)))(N,V0,G1)),V0,G1),s.negate((lambda var7,var8,var9:s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,var8))),s.reciprocal(s.plus(1,s.times(1,s.times(var7,var9))))))((lambda var10,var11,var12:s.plus(s.times((lambda var13:s.plus(s.times(s.times(1,s.reciprocal(s.times(1,s.times(1,1)))),s.plus(1,s.times(1,var13))),s.negate(s.times(1,s.reciprocal(1)))))(var11),s.reciprocal(var12)),s.negate(var10)))(N,V0,G1),V0,G1)))),s.plus(s.times(EXPT_GAMMA_1,s.plus((lambda var14,var15,var16:s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,var15))),s.reciprocal(s.plus(1,s.times(1,s.times(var14,var16))))))((lambda var17,var18,var19:s.plus(s.times((lambda var20:s.plus(s.times(s.times(1,s.reciprocal(s.times(1,s.times(1,1)))),s.plus(1,s.times(1,var20))),s.negate(s.times(1,s.reciprocal(1)))))(var18),s.reciprocal(var19)),s.negate(var17)))(N,V0,G1),V0,G1),s.negate((lambda var21,var22,var23:s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,var22))),s.reciprocal(s.plus(1,s.times(1,s.times(var21,var23))))))(s.plus(1,(lambda var24,var25,var26:s.plus(s.times((lambda var27:s.plus(s.times(s.times(1,s.reciprocal(s.times(1,s.times(1,1)))),s.plus(1,s.times(1,var27))),s.negate(s.times(1,s.reciprocal(1)))))(var25),s.reciprocal(var26)),s.negate(var24)))(N,V0,G1)),V0,G1)))),s.plus(-1,s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,V0))),s.reciprocal(s.plus(1,s.times(1,s.plus(s.times(G1,s.plus(1,s.negate(N))),(lambda var28:s.plus(s.times(s.times(1,s.reciprocal(s.times(1,s.times(1,1)))),s.plus(1,s.times(1,var28))),s.negate(s.times(1,s.reciprocal(1)))))(V0))))))))),s.reciprocal(s.plus(1,s.negate(s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,V0))),s.reciprocal(s.plus(1,s.times(1,s.plus(s.times(G1,s.plus(-1,N)),(lambda var29:s.plus(s.times(s.times(1,s.reciprocal(s.times(1,s.times(1,1)))),s.plus(1,s.times(1,var29))),s.negate(s.times(1,s.reciprocal(1)))))(V0)))))))))),s.times(2,N)),s.lt(s.times(s.plus(s.times(EXPT_GAMMA_2,s.plus((lambda var30,var31,var32:s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,var31))),s.reciprocal(s.plus(1,s.times(1,s.times(var30,var32))))))(s.plus(-1,(lambda var33,var34,var35:s.plus(s.times((lambda var36:s.plus(s.times(s.times(1,s.reciprocal(s.times(1,s.times(1,1)))),s.plus(1,s.times(1,var36))),s.negate(s.times(1,s.reciprocal(1)))))(var34),s.reciprocal(var35)),s.negate(var33)))(N,V0,G1)),V0,G1),s.negate((lambda var37,var38,var39:s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,var38))),s.reciprocal(s.plus(1,s.times(1,s.times(var37,var39))))))((lambda var40,var41,var42:s.plus(s.times((lambda var43:s.plus(s.times(s.times(1,s.reciprocal(s.times(1,s.times(1,1)))),s.plus(1,s.times(1,var43))),s.negate(s.times(1,s.reciprocal(1)))))(var41),s.reciprocal(var42)),s.negate(var40)))(N,V0,G1),V0,G1)))),s.plus(s.times(EXPT_GAMMA_1,s.plus((lambda var44,var45,var46:s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,var45))),s.reciprocal(s.plus(1,s.times(1,s.times(var44,var46))))))((lambda var47,var48,var49:s.plus(s.times((lambda var50:s.plus(s.times(s.times(1,s.reciprocal(s.times(1,s.times(1,1)))),s.plus(1,s.times(1,var50))),s.negate(s.times(1,s.reciprocal(1)))))(var48),s.reciprocal(var49)),s.negate(var47)))(N,V0,G1),V0,G1),s.negate((lambda var51,var52,var53:s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,var52))),s.reciprocal(s.plus(1,s.times(1,s.times(var51,var53))))))(s.plus(1,(lambda var54,var55,var56:s.plus(s.times((lambda var57:s.plus(s.times(s.times(1,s.reciprocal(s.times(1,s.times(1,1)))),s.plus(1,s.times(1,var57))),s.negate(s.times(1,s.reciprocal(1)))))(var55),s.reciprocal(var56)),s.negate(var54)))(N,V0,G1)),V0,G1)))),s.plus(-1,s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,V0))),s.reciprocal(s.plus(1,s.times(1,s.plus(s.times(G1,s.plus(1,s.negate(N))),(lambda var58:s.plus(s.times(s.times(1,s.reciprocal(s.times(1,s.times(1,1)))),s.plus(1,s.times(1,var58))),s.negate(s.times(1,s.reciprocal(1)))))(V0))))))))),s.reciprocal(s.plus(1,s.negate(s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,V0))),s.reciprocal(s.plus(1,s.times(1,s.plus(s.times(G1,s.plus(-1,N)),(lambda var59:s.plus(s.times(s.times(1,s.reciprocal(s.times(1,s.times(1,1)))),s.plus(1,s.times(1,var59))),s.negate(s.times(1,s.reciprocal(1)))))(V0)))))))))),EXPT_GAMMA_2_MINUS_2N))
s.prove(hypothesis, conclusion)

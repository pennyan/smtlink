from sys import path
path.insert(0,"/ubc/cs/home/y/yanpeng/project/ACL2/smtlink/z3_interface")
from ACL2_translator import to_smt, Q
s = to_smt()
EXPT_GAMMA_1_MINUS_N=s.isReal("EXPT_GAMMA_1_MINUS_N")
EXPT_GAMMA_N_MINUS_1=s.isReal("EXPT_GAMMA_N_MINUS_1")
EXPT_GAMMA_2N_MINUS_1=s.isReal("EXPT_GAMMA_2N_MINUS_1")
EXPT_GAMMA_2N=s.isReal("EXPT_GAMMA_2N")
N=s.isReal("N")
DC=s.isReal("DC")
G1=s.isReal("G1")
V0=s.isReal("V0")
DV=s.isReal("DV")
hypothesis=s.ifx(s.notx(s.lt(N,3)),s.ifx(s.notx(s.lt(640,N)),s.ifx(s.notx(s.lt(DC,0)),s.ifx(s.lt(DC,1),s.ifx(s.equal(G1,Q(1,3200)),s.ifx(s.notx(s.lt(V0,Q(9,10))),s.ifx(s.notx(s.lt(Q(11,10),V0)),s.ifx(s.notx(s.lt(DV,s.negate(s.times(-2,Q(-1,16000))))),s.notx(s.lt(s.times(-2,Q(-1,16000)),DV)),False),False),False),False),False),False),False),False)
conclusion=s.equal(s.plus(s.plus(s.times(EXPT_GAMMA_2N,s.plus(-1,(lambda var0,var1,var2,var3,var4:s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,s.plus(var1,var2)))),s.reciprocal(s.plus(1,s.times(1,s.times(s.plus(var0,var4),var3))))))(s.plus(-1,(lambda var5,var6,var7:s.plus(s.times((lambda var8:s.plus(s.times(1,s.times(s.plus(1,s.times(1,var8)),s.reciprocal(s.times(1,s.times(1,1))))),s.negate(s.reciprocal(1))))(var6),s.reciprocal(var7)),s.negate(var5)))(N,V0,G1)),V0,DV,G1,DC))),s.negate(s.times(EXPT_GAMMA_2N,s.plus(-1,(lambda var9,var10,var11,var12,var13:s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,s.plus(var10,var11)))),s.reciprocal(s.plus(1,s.times(1,s.times(s.plus(var9,var13),var12))))))((lambda var14,var15,var16:s.plus(s.times((lambda var17:s.plus(s.times(1,s.times(s.plus(1,s.times(1,var17)),s.reciprocal(s.times(1,s.times(1,1))))),s.negate(s.reciprocal(1))))(var15),s.reciprocal(var16)),s.negate(var14)))(N,V0,G1),V0,DV,G1,DC))))),s.plus(s.plus(s.times(EXPT_GAMMA_2N_MINUS_1,s.plus(-1,(lambda var18,var19,var20,var21,var22:s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,s.plus(var19,var20)))),s.reciprocal(s.plus(1,s.times(1,s.times(s.plus(var18,var22),var21))))))((lambda var23,var24,var25:s.plus(s.times((lambda var26:s.plus(s.times(1,s.times(s.plus(1,s.times(1,var26)),s.reciprocal(s.times(1,s.times(1,1))))),s.negate(s.reciprocal(1))))(var24),s.reciprocal(var25)),s.negate(var23)))(N,V0,G1),V0,DV,G1,DC))),s.negate(s.times(EXPT_GAMMA_2N_MINUS_1,s.plus(-1,(lambda var27,var28,var29,var30,var31:s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,s.plus(var28,var29)))),s.reciprocal(s.plus(1,s.times(1,s.times(s.plus(var27,var31),var30))))))(s.plus(1,(lambda var32,var33,var34:s.plus(s.times((lambda var35:s.plus(s.times(1,s.times(s.plus(1,s.times(1,var35)),s.reciprocal(s.times(1,s.times(1,1))))),s.negate(s.reciprocal(1))))(var33),s.reciprocal(var34)),s.negate(var32)))(N,V0,G1)),V0,DV,G1,DC))))),s.times(EXPT_GAMMA_N_MINUS_1,s.plus(s.times(EXPT_GAMMA_1_MINUS_N,s.plus(-1,s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,s.plus(V0,DV)))),s.reciprocal(s.plus(1,s.times(1,s.plus(s.times(G1,s.plus(s.plus(-1,N),DC)),(lambda var36:s.plus(s.times(1,s.times(s.plus(1,s.times(1,var36)),s.reciprocal(s.times(1,s.times(1,1))))),s.negate(s.reciprocal(1))))(V0)))))))),s.times(EXPT_GAMMA_N_MINUS_1,s.plus(-1,s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,s.plus(V0,DV)))),s.reciprocal(s.plus(1,s.times(1,s.plus(s.times(G1,s.plus(s.plus(1,s.negate(N)),DC)),(lambda var37:s.plus(s.times(1,s.times(s.plus(1,s.times(1,var37)),s.reciprocal(s.times(1,s.times(1,1))))),s.negate(s.reciprocal(1))))(V0)))))))))))),s.plus(s.times(EXPT_GAMMA_2N,s.plus((lambda var38,var39,var40,var41,var42:s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,s.plus(var39,var40)))),s.reciprocal(s.plus(1,s.times(1,s.times(s.plus(var38,var42),var41))))))(s.plus(-1,(lambda var43,var44,var45:s.plus(s.times((lambda var46:s.plus(s.times(1,s.times(s.plus(1,s.times(1,var46)),s.reciprocal(s.times(1,s.times(1,1))))),s.negate(s.reciprocal(1))))(var44),s.reciprocal(var45)),s.negate(var43)))(N,V0,G1)),V0,DV,G1,DC),s.negate((lambda var47,var48,var49,var50,var51:s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,s.plus(var48,var49)))),s.reciprocal(s.plus(1,s.times(1,s.times(s.plus(var47,var51),var50))))))((lambda var52,var53,var54:s.plus(s.times((lambda var55:s.plus(s.times(1,s.times(s.plus(1,s.times(1,var55)),s.reciprocal(s.times(1,s.times(1,1))))),s.negate(s.reciprocal(1))))(var53),s.reciprocal(var54)),s.negate(var52)))(N,V0,G1),V0,DV,G1,DC)))),s.plus(s.times(EXPT_GAMMA_2N_MINUS_1,s.plus((lambda var56,var57,var58,var59,var60:s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,s.plus(var57,var58)))),s.reciprocal(s.plus(1,s.times(1,s.times(s.plus(var56,var60),var59))))))((lambda var61,var62,var63:s.plus(s.times((lambda var64:s.plus(s.times(1,s.times(s.plus(1,s.times(1,var64)),s.reciprocal(s.times(1,s.times(1,1))))),s.negate(s.reciprocal(1))))(var62),s.reciprocal(var63)),s.negate(var61)))(N,V0,G1),V0,DV,G1,DC),s.negate((lambda var65,var66,var67,var68,var69:s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,s.plus(var66,var67)))),s.reciprocal(s.plus(1,s.times(1,s.times(s.plus(var65,var69),var68))))))(s.plus(1,(lambda var70,var71,var72:s.plus(s.times((lambda var73:s.plus(s.times(1,s.times(s.plus(1,s.times(1,var73)),s.reciprocal(s.times(1,s.times(1,1))))),s.negate(s.reciprocal(1))))(var71),s.reciprocal(var72)),s.negate(var70)))(N,V0,G1)),V0,DV,G1,DC)))),s.plus(s.times(s.times(EXPT_GAMMA_N_MINUS_1,EXPT_GAMMA_1_MINUS_N),s.plus(-1,s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,s.plus(V0,DV)))),s.reciprocal(s.plus(1,s.times(1,s.plus(s.times(G1,s.plus(s.plus(-1,N),DC)),(lambda var74:s.plus(s.times(1,s.times(s.plus(1,s.times(1,var74)),s.reciprocal(s.times(1,s.times(1,1))))),s.negate(s.reciprocal(1))))(V0)))))))),s.times(s.times(EXPT_GAMMA_N_MINUS_1,EXPT_GAMMA_N_MINUS_1),s.plus(-1,s.times(s.times(s.times(1,s.reciprocal(s.times(1,1))),s.plus(1,s.times(1,s.plus(V0,DV)))),s.reciprocal(s.plus(1,s.times(1,s.plus(s.times(G1,s.plus(s.plus(1,s.negate(N)),DC)),(lambda var75:s.plus(s.times(1,s.times(s.plus(1,s.times(1,var75)),s.reciprocal(s.times(1,s.times(1,1))))),s.negate(s.reciprocal(1))))(V0))))))))))))
s.prove(hypothesis, conclusion)

from sys import path
path.insert(0,"/ubc/cs/home/y/yanpeng/project/ACL2/smtlink/z3_interface")
from ACL2_translator import to_smt
s = to_smt()
*G1*=1
s.isReal("M")
hypothesis=s.ifx(s.notx(s.lt(s.plus(-3,s.times(s.let(['',False]).inn(s.plus(s.times(s.times(1,s.reciprocal(s.times(1,s.times(1,1)))),s.plus(1,s.times(1,1))),s.negate(s.times(1,s.reciprocal(1))))),s.reciprocal(1/3200))),s.getVar('M'))),s.notx(s.lt(s.getVar('M'),s.plus(-320,s.times(s.let(['',False]).inn(s.plus(s.times(s.times(1,s.reciprocal(s.times(1,s.times(1,1)))),s.plus(1,s.times(1,1))),s.negate(s.times(1,s.reciprocal(1))))),s.reciprocal(1/3200))))),False)
conclusion=s.lt(s.plus(s.let([['var0',s.plus(s.unknown(1),s.plus(s.unknown(-2),s.let(['var4',s.getVar('M')]).inn(s.plus(s.times(s.unknown(),s.reciprocal(s.unknown(1/3200))),s.negate(s.getVar('var4'))))))],['var1',s.getVar('ARGS')]]).inn(s.times(False,s.plus(-1,s.times(s.times(False,s.plus(1,s.times(1,1))),s.reciprocal(s.plus(1,s.times(1,False))))))),s.let([['var2',s.plus(s.plus(s.plus(s.unknown(-1),s.let(['var5',s.getVar('M')]).inn(s.plus(s.times(s.unknown(),s.reciprocal(s.unknown(1/3200))),s.negate(s.getVar('var5'))))),s.negate(s.plus(s.unknown(-2),s.let(['var6',s.getVar('M')]).inn(s.plus(s.times(s.unknown(),s.reciprocal(s.unknown(1/3200))),s.negate(s.getVar('var6'))))))),s.let(['var7',s.getVar('M')]).inn(s.plus(s.times(s.unknown(),s.reciprocal(s.unknown(1/3200))),s.negate(s.getVar('var7')))))],['var3',s.getVar('ARGS')]]).inn(s.times(False,s.plus(-1,s.times(s.times(False,s.plus(1,s.times(1,1))),s.reciprocal(s.plus(1,s.times(1,False)))))))),0)
s.prove(hypothesis, conclusion)

from sys import path
path.insert(0,"/ubc/cs/home/y/yanpeng/project/ACL2/smtlink/z3_interface")
from ACL2_translator import to_smt
s = to_smt()
CONST1=1
s.isReal("X")
s.isReal("Y")
s.isReal("Z")
hypothesis=s.ifx(s.notx(s.notx(s.lt(0,s.getVar('X')))),s.ifx(s.equal(s.getVar('Z'),s.plus(2,4)),s.ifx(s.lt(s.getVar('Y'),s.getVar('X')),s.lt(s.getVar('Y'),s.getVar('X')),s.lt(s.plus(s.getVar('Y'),1),s.getVar('X'))),False),False)
conclusion=s.lt(s.let([['var0',s.getVar('X')],['var1',s.getVar('Y')]]).inn(s.times(s.getVar('var0'),s.getVar('var1'))),s.let([['var2',s.getVar('X')],['var3',s.let([['var4',s.getVar('X')],['var5',s.getVar('Z')]]).inn(s.times(s.getVar('var4'),s.getVar('var5')))]]).inn(s.times(s.getVar('var2'),s.getVar('var3'))))
s.prove(hypothesis, conclusion)

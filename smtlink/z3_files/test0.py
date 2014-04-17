from sys import path
path.insert(0,"/ubc/cs/home/y/yanpeng/project/ACL2/smtlink/z3_interface")
from ACL2_translator import to_smt
s = to_smt()
s.isReal("X")
hypothesis=True
conclusion=s.equal(s.plus(s.getVar('X'),s.getVar('X')),s.let(['var0',s.getVar('X')]).inn(s.times(2,s.getVar('var0'))))
s.prove(hypothesis, conclusion)


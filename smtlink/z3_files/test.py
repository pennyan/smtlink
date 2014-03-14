import sys
sys.path.insert(0,"z3_interface")
from ACL2_translator import *
hypothesis=
conclusion=
prove(Implies(hypothesis, conclusion))

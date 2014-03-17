# This is a Z3 file that provides a set of python functions
# for the translating middle code from ACL2 to Z3 code
from z3 import *

# These two functions are redundant
# def acl2_isreal(x): return "Real(" + x + ")"
# def acl2_isint(x): return "Int(" + x + ")"

def acl2_plus(*args):
   sum = 0	
   for a in args:
     sum = sum + a
   return sum	

def acl2_multiply(*args): 
	product = 1
	for a in args:
		product = product * a
	return product

def acl2_and(*args):
	conjunction = True
	for a in args:
		conjunction = And(conjunction, a) 
	return conjunction

def acl2_or(*args):
	disjunction = False
	for a in args:
		disjunction = Or(disjunction, a) 
	return disjunction

def acl2_minus(x,y): return x-y
def acl2_divide(x,y): return x/y
def acl2_gt(x,y): return x>y
def acl2_st(x,y): return x<y
def acl2_get(x,y): return x>=y
def acl2_set(x,y): return x<=y
def acl2_equal(x,y): return x==y
def acl2_not(x): return Not(x)

# Special treatment for if statement
x_bool = Bool('x_bool')
y_bool = Bool('y_bool')
x_real = Real('x_real')
y_real = Real('y_real')
x_int = Int('x_int')
y_int = Int('y_int')

acl2_if_bool = Function('acl2_if_bool', \
                        BoolSort(), \
                        BoolSort(), \
                        BoolSort(), \
                        BoolSort())
acl2_if_real = Function('acl2_if_real', \
                        BoolSort(), \
                        RealSort(), \
                        RealSort(), \
                        RealSort())
acl2_if_int = Function('acl2_if_int', \
                       BoolSort(), \
                       IntSort(), \
                       IntSort(), \
                       IntSort())

if_constraint_bool = And((acl2_if_bool(True, x_bool, y_bool) \
                     == x_bool) \
                    (acl2_if_bool(False, x_bool, y_bool) \
                     == y_bool))
if_constraint_real = And((acl2_if_real(True, x_real, y_real) \
                     == x_real) \
                    (acl2_if_real(False, x_real, y_real) \
                     == y_real))
if_constraint_int = And((acl2_if_int(True, x_int, y_int) \
                         == x_int) \
                    (acl2_if_int(False, x_int, y_int) \
                     == y_int))

def acl2_if(condx, thenx, elsex):
   try: 
      if(thenx.sort() == BoolSort() and elsex.sort() == BoolSort()):
         return acl2_if_bool(condx, thenx, elsex)
      elif(thenx.sort() == RealSort() and elsex.sort() == RealSort()):
         return acl2_if_real(condx, thenx, elsex)
      elif(thenx.sort() == IntSort() and elsex.sort() == IntSort()):
         return acl2_if_int(condx, thenx, elsex)
   except:
      print "if statement's then statement and else statement type mismatch."

      

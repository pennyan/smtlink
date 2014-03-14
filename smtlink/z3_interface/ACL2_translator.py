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
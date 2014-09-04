# GlGates.py -- primitive logic functions that operate on GlBool signals
#
# Define a Z3 "sort" (i.e., type) with boolean values that may
#     change over time as described below:
#
#   'lo'   -> constant low (false)
#   'hi'   -> constant high (true)
#   'up'   -> a single low-to-high transition, starts low and ends high.
#               The time of the transition is not specified.
#   'dn'   -> a single high-to-low transition, starts high and ends low.
#               The time of the transition is not specified.
#   'g010' -> an up-glitch, starts low, goes high for a while, returns to low.
#               The times of the transitions are not specified.
#               The signal may stay low the entire time.
#   'g101' -> a down-glitch, starts high, goes low for a while, returns to high.
#               The times of the transitions are not specified.
#               The signal may stay high the entire time.
#   'X'    -> anything (including the behaviors listed above)
#
# Mark R. Greenstreet, Oracle Labs, 18 June 2013
# Adapted from Ian W. Jones's, boolean_xy.py (5 June 2013) and
# logic_xy_gates.py (5 June 2013)


from z3       import *
from GlBool   import *    # definition of the glitch & boolean signal waveform 'type': GlBool


# Now, I'll define the 'not' operation.  I'll write a few 'wrong'
# versions first to illustrate how z3 and python interact.

# GlWrongNot(a):
#   This one is based on Ian's code from logic_xy_gates.
#   It uses the python if(x is Constant) construction.
#   However, z3 wants a symbolic expression, thus, there is no specific
#   value of 'a' to compare against the various values for a GlBool.
#   Thus, GlWrongNot ends up throwing an exception when used with
#   z3's solve function.
def GlWrongNot(a) :
	out = Const('out', GlBool)
	if   a is GlBool.lo   : out = GlBool.hi
	elif a is GlBool.hi   : out = GlBool.lo
	elif a is GlBool.up   : out = GlBool.up
	elif a is GlBool.dn   : out = GlBool.dn
	elif a is GlBool.g010 : out = GlBool.g010
	elif a is GlBool.g101 : out = GlBool.g101
	elif a is GlBool.X    : out = GlBool.X
	else :
		err_msg = "GlWrongNot: Illegal input: a = {0}".format(a)
		raise Exception(err_msg)
	return out

def GlTestWrongNot(val=GlBool.lo) :
	# feel free to ignore the next three lines, I'm just catching arguments
	#   that I'm not prepared to handle.
	if (not is_const(val)) or (val.decl().kind() == Z3_OP_UNINTERPRETED) :
		err_msg = "GlTestWrongNot(val): val should be a fixed value (not symbolic)"
		raise Exception(err_msg)
	print "GlTestWrongNot: solve(Not(a)=={0})".format(val)
	print "  We would hope to get '{0}', but we get an Exception instead".format( GlWrongNot(val))
	a = Const('a', GlBool)
	solve(GlWrongNot(a)==val)


# GlClumsyNot(a):
#   Instead of using python's if-then-else control construct, we
#   use z3's If(condition, thenClause, elseClause) function.
#   This produces a big expression that is what we mean by 'not'.
#
#   Notes:
#   1. "==" is overloaded by Z3 such that "a == GlBool.hi" produces a symbolic value rather than evaluating the exression.
#   2. "If" is a Z3 function which symbolically perfoms the if, while "if" is a Python control operator!
#
def GlClumsyNot(a) :
	out = Const('out', GlBool)
	out = \
		If(a == GlBool.hi,   GlBool.lo,
			If(a == GlBool.lo,   GlBool.hi,
				If(a == GlBool.up,   GlBool.dn,
					If(a == GlBool.dn,   GlBool.up,
						If(a == GlBool.g010, GlBool.g101,
							If(a == GlBool.g101, GlBool.g010, GlBool.X))))))
	return out

def GlTestClumsyNot(val=GlBool.lo) :
	print "Find a solution for: Not(a)={0}".format(val)
	a = Const('a', GlBool)
	solve(GlClumsyNot(a)==val)


# GlCond(list of (condition, value) pairs):
#   GlClumsyNot works, but it's going to get really annoying to write
#   deeply nested expressions.  What we want is a lisp-style cond.
#   GlCond([(c1, v1), (c2, v2), ... (cn, vn)]) returns the expression
#     If(c1, v1, If(c2, v2, If(..., If(cn, vn, GlBool.X)...)))
#   z3 requires functions to be total (have a value for all values of
#   their arguments); so we need to provide a value in the case that
#   none of the conditions are satisfied.  In this case, GlCond returns
#   GlBool.X -- in English, that means "I don't know.".
#
# Note:
#  1. the "If(stuff[0][0], stuff[0][1], GlCond(stuff[1:]))" returns the Z3
#     expression for all the whole list of "stuff". i.e.,
#     this expression says if the first condition is satisfied produce the first value
#     and the else clause for Z3 is the expression for the tail of "stuff".
def GlCond(stuff) :
	if stuff :   # this is Python for "stuff" is not empty
		return If(stuff[0][0], stuff[0][1], GlCond(stuff[1:]))
	else :
		return GlBool.X

# GlGet(list of (key, value) pairs, key0):
#   Return 'value' for the first tuple whose 'key' matches 'key0'.
#   If no such 'value' exists, return GlBool.X
def GlGet(key0, stuff) :
	if stuff :
		return If(stuff[0][0]==key0, stuff[0][1], GlGet(key0, stuff[1:]))
	else :
		return GlBool.X


# GlPenultimateNot :  I'll use GlCond to clean-up GlClumsyNot.
#   After this works, I'll tidy up a few more details to produce
#   the version we really want.
def GlPenultimateNot(a) :
	out = Const('out', GlBool)
	out = GlGet(a, [(GlBool.lo,   GlBool.hi),   (GlBool.hi,   GlBool.lo),
			(GlBool.up,   GlBool.dn),   (GlBool.dn,   GlBool.up),
			(GlBool.g010, GlBool.g101), (GlBool.g101, GlBool.g010),
			(GlBool.X,    GlBool.X)])
	return out

def GlTestPenultimateNot(val=GlBool.lo) :
	print "Find a solution for: Not(a)={0}".format(val)
	a = Const('a', GlBool)
	solve(GlPenultimateNot(a)==val)


# GlNot :
#   We now note that the 'out' variable in the previous versions is unneeded.
#   The statement: out = Const('out', GlBool)  creates a new symbolic variable
#   of sort GlBool, with symbolic name 'out' and assigns it to the python
#   variable out.  In each version, this was followed by a statement of the
#   form: out = expr
#   This overwrites the python variable called 'out' with a new value.
#   The symbolic variable produced in the earlier statement is never used.
#   So, we don't need to create it.  Furthermore, we can just return the
#   value of expr, and we don't need to assign it to a python variable first.
#   Here's the code.
def GlNot(a) :
	return GlGet(a, [ (GlBool.lo,   GlBool.hi),   (GlBool.hi,   GlBool.lo),
			  (GlBool.up,   GlBool.dn),   (GlBool.dn,   GlBool.up),
			  (GlBool.g010, GlBool.g101), (GlBool.g101, GlBool.g010),
			  (GlBool.X,    GlBool.X)])

def GlTestNot(val=GlBool.lo) :
	print "Find a solution for: Not(a)={0}".format(val)
	a = Const('a', GlBool)
	solve(GlNot(a)==val)


# Now that we've mastered GlNot(a), let's try GlAnd(a, b)
def GlFirstTryAnd(a, b) :
	return GlCond([
		(a==GlBool.lo, a), (a==GlBool.hi, b),
		(b==GlBool.lo, b), (b==GlBool.hi, a),
		# thus neither input is lo, or hi
		(Or(a==GlBool.g101, a==GlBool.X, b==GlBool.X, b==GlBool.g101), GlBool.X),
		# thus neither input is a 101 or an X, leaving up, dn, and g010
		# recall that "(GlBool.dn, GlBool.g010)" covers the case where the ouput is a constant lo
		# due to the definition of g010 including the always lo situation
		(a==GlBool.up, GlGet(b, [
			(GlBool.up, b), (GlBool.dn, GlBool.g010), (GlBool.g010, b),
			])),
		(a==GlBool.dn, GlGet(b, [
			(GlBool.up, GlBool.g010), (GlBool.dn, GlBool.dn), (GlBool.g010, b),
			])),
		# leaving the remaining case that a is an up glitch
		(a==GlBool.g010, a)
		])
		
def GlTestFirstTryAnd(a=GlBool.up, y=GlBool.g010) :
	print "Find b s.t. for: GlAnd(a,b)={0}".format(y)
	b = Const('b', GlBool)
	solve(GlFirstTryAnd(a,b)==y)


# GlAnd(...) : Just as z3 allows And to take an arbitrary number of arguments,
# we'll do the same.
def GlAnd(*args) :
	nargs = len(args)
	if nargs==0   : return(BlBool.hi)
	elif nargs==1 : return(args[0])
	elif nargs==2 :
		a = args[0]
		b = args[1]
		return GlCond([
			(a==GlBool.lo, a), (a==GlBool.hi, b),
			(b==GlBool.lo, b), (b==GlBool.hi, a),
			(Or(a==GlBool.g101, a==GlBool.X, b==GlBool.X, b==GlBool.g101), GlBool.X),
			(a==GlBool.up, GlGet(b, [
				(GlBool.up, b), (GlBool.dn, GlBool.g010), (GlBool.g010, b),
				])),
			(a==GlBool.dn, GlGet(b, [
				(GlBool.up, GlBool.g010), (GlBool.dn, GlBool.dn), (GlBool.g010, b),
				])),
			(a==GlBool.g010, a)
			])
	else : return GlAnd(GlAnd(args[0], args[1]), *args[2:])

# Added by Yan to try out the idea that up, dn, g010 and g101 can be replaced with just using X
# GlAndX: take g010 g101 up and dn all to be just X
def GlAndX(*args):
        nargs = len(args)
	if nargs==0   : return(BlBool.hi)
	elif nargs==1 : return(args[0])
	elif nargs==2 :
		a = args[0]
		b = args[1]
		return GlCond([
			(a==GlBool.lo, a), (a==GlBool.hi, b),
			(b==GlBool.lo, b), (b==GlBool.hi, a),
			(Or(a==GlBool.X, b==GlBool.X), GlBool.X)
			])
	else : return GlAnd(GlAnd(args[0], args[1]), *args[2:])
		
def GlTestAnd(a=GlBool.up, y=GlBool.g010) :
	print "Find b and c s.t. for: GlAnd(a,b,c)={0}".format(y)
	b = Const('b', GlBool)
	c = Const('c', GlBool)
	solve(GlAnd(a,b,c)==y)


# GlOr(...) : I'll use De Morgan's Law until someone shows me that this causes
# a significant slow-down for z3.
def GlOr(*args) : return GlNot(GlAnd(*[GlNot(x) for x in args]))


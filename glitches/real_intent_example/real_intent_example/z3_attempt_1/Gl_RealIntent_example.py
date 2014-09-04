# Gl_RealIntent_example.py
#
# Ian W. Jones, 6 August 2014
#
# Show that the Synthesised Real Intent MUX example contains a logic hazard
# compared to the original RTL definition.
# Enumerates the multiple examples where the two mux circuits differ.
#
#
# This code is based on the GlMuxGold.py example by Mark Greenstreet and Ian W. Jones, 23 July 2013
# that was originally based on mux_equivalence.py by Ian W. Jones (7 May 2013)
#

from z3       import *
from GlBool   import *    # definition of the glitch & boolean signal waveform 'type': GlBool
from GlGates  import *    # and the GlNot, GlAnd, and GlOr functions

# add some z3 versions of some python built-ins
def All(stuff) : return reduce(And, stuff)
def Any(stuff) : return reduce(Or,  stuff)

# stable(x) is true if x is a value that is known not to change
def stable(x) : return Or(x==GlBool.lo, x==GlBool.hi)

# xify(x) : preserver lo and hi values, everything else becomes x
def xify(x=GlBool.X) : return GlCond([(stable(x), x)])


# mux gate
def GlMux(in0, in1, sel) :
    return GlOr(GlAnd(sel, in1), GlAnd(GlNot(sel), in0))


# the original Real Intent mux with 2 data inputs ANDed together -- that we use as the "gold" reference:
def mux_ri_gold(a0, d1a, d1b, sel) :
	return GlMux(a0, GlAnd(d1a, d1b), sel)


# Real Intent's "optimized" mux:
def mux_ri_opt(a0, d1a, d1b, sel) :
	return GlOr( \
		    GlAnd(a0,  d1a, d1b), \
		    GlAnd(sel, d1a, d1b, GlNot(a0)), \
		    GlAnd(GlNot(sel), d1a, GlNot(d1b), a0), \
	        GlAnd(GlNot(d1a), GlNot(sel), a0) \
		    )


def GlMuxRITest(maxNumCounterExamples = 10) :
	print "==============================================================================================="
	print "Running GlMuxRITest with: maxNumCounterExamples = ", maxNumCounterExamples
	print "==============================================================================================="
	
	a0,  d1a,  d1b,  sel = GlBools('a0  d1a  d1b  sel')
	inputs    = [a0, d1a, d1b, sel]    # all inputs
	inputs1   = [a0, sel]              # the set of 'single cycle' stable inputs

	stableAll = All([stable(x) for x in inputs])
	stable1   = All([stable(x) for x in inputs1])

	# show that these two muxes are logically equivalent when used in a fully 'single-cycle' environment:
	print "Verify that the mux_ri_gold and mux_ri_opt are logically equivalent when used in a fully 'single-cycle' environment:"
	
	s = Solver();

	# when all inputs are stable:
	s.add(stableAll)
	
	# the "gold" standard behaviour: the mux_ri_gold behaviour when a0 and sel are stable and a1 is
	# either stable or X (xify is emplyed to convert glitches to X), such that the output is a stable signal:
	# s.add(stable(mux_ri_gold(a0, xify(d1a), xify(d1b), sel)))
        s.add(stable(mux_ri_gold(a0, d1a, d1b, sel)))

	# when mux_ri_opt behaviour does not match that of mux_ri_gold:
	s.add(mux_ri_opt(a0, d1a, d1b, sel) != mux_ri_gold(a0, d1a, d1b, sel))


	
	solution = (s.check() == sat)

	if solution :
		print "The muxes are NOT logically equivalent in a 'single-cycle' environment -- this is unexpected!"
		x = s.model()         # one example where the muxes do not match
		print "Here's an example where they differ: {0}".format(x)
	else:
		print "The muxes are logically equivalent in a 'single-cycle' environment -- as expected."

	print "\n"



	# Now check that these muxes differ when the d1a and d1b inputs are multi-cycle or asynchronous inputs	


	print "Verify that the mux_ri_gold and mux_ri_opt are different,"
	print "expect that they will differ when sel is lo, and d1a and d1b are glitch inputs:"

	
	s = Solver();

	# when all 'single cycle' inputs are stable:
	s.add(stable1)
	
	# the "gold" standard behaviour: the mux_ri_gold behaviour when a0 and sel are stable and a1 is
	# either stable or X (xify is emplyed to convert glitches to X), such that the output is a stable signal:
	# s.add(stable(mux_ri_gold(a0, xify(d1a), xify(d1b), sel)))
        s.add(stable(mux_ri_gold(a0, d1a, d1b, sel)))

	# when mux_ri_opt behaviour does not match that of mux_ri_gold:
	s.add(mux_ri_opt(a0, d1a, d1b, sel) != mux_ri_gold(a0, d1a, d1b, sel))

	# reduce the number of fail cases by contraining d1b to be hi:
	##s.add (d1b == GlBool.hi)


	solution_counter = 0
	
	while (solution_counter <  maxNumCounterExamples) and (s.check() == sat) :
		solution_counter = solution_counter + 1
		x = s.model() # one of the examples where the muxes do not match
		print "The mux circuits differ, here's an example #{0:3d}:  {1}.".format(solution_counter, x)
		y = []
		for z in x:
			y.append(z() == x[z])		
		s.add(Not(And(y)))  # exclude the example just found
	
	more_solutions = (s.check() == sat)
	
	if 0 == maxNumCounterExamples :
		if more_solutions :
			print "Example where muxes differ found -- details omitted!"
		else :
			print "No examples where the muxes differ found!"		
	elif 0 == solution_counter :
			print "No examples where the muxes differ found!"		
	else :
		if more_solutions :
			print "There is at least one more example where the muxes differ!"
		else :
			print "We have found all {0} example cases where the muxes differ.".format(solution_counter)

	print "\n"



[GlMuxRITest(n) for n in [0, 1, 42] ]  # run the test when this file is loaded

# Produces the following output:
#
# iwjones% python Gl_RealIntent_example.py
# ===============================================================================================
# Running GlMuxRITest with: maxNumCounterExamples =  0
# ===============================================================================================
# Verify that the mux_ri_gold and mux_ri_opt are logically equivalent when used in a fully 'single-cycle' environment:
# The muxes are logically equivalent in a 'single-cycle' environment -- as expected.
# 
# 
# Verify that the mux_ri_gold and mux_ri_opt are different,
# expect that they will differ when sel is lo, and d1a and d1b are glitch inputs:
# Example where muxes differ found -- details omitted!
# 
# 
# ===============================================================================================
# Running GlMuxRITest with: maxNumCounterExamples =  1
# ===============================================================================================
# Verify that the mux_ri_gold and mux_ri_opt are logically equivalent when used in a fully 'single-cycle' environment:
# The muxes are logically equivalent in a 'single-cycle' environment -- as expected.
# 
# 
# Verify that the mux_ri_gold and mux_ri_opt are different,
# expect that they will differ when sel is lo, and d1a and d1b are glitch inputs:
# The mux circuits differ, here's an example #  1:  [a0 = hi, sel = lo, d1b = lo, d1a = g101]
# There is at least one more example where the muxes differ!
# 
# 
# ===============================================================================================
# Running GlMuxRITest with: maxNumCounterExamples =  42
# ===============================================================================================
# Verify that the mux_ri_gold and mux_ri_opt are logically equivalent when used in a fully 'single-cycle' environment:
# The muxes are logically equivalent in a 'single-cycle' environment -- as expected.
# 
# 
# Verify that the mux_ri_gold and mux_ri_opt are different,
# expect that they will differ when sel is lo, and d1a and d1b are glitch inputs:
# The mux circuits differ, here's an example #  1:  [a0 = hi, sel = lo, d1b = lo, d1a = g101]
# The mux circuits differ, here's an example #  2:  [a0 = hi, sel = lo, d1b = lo, d1a = g010]
# The mux circuits differ, here's an example #  3:  [a0 = hi, sel = lo, d1b = lo, d1a = X]
# The mux circuits differ, here's an example #  4:  [a0 = hi, sel = lo, d1b = lo, d1a = up]
# The mux circuits differ, here's an example #  5:  [a0 = hi, sel = lo, d1b = g010, d1a = up]
# The mux circuits differ, here's an example #  6:  [a0 = hi, sel = lo, d1b = g010, d1a = dn]
# The mux circuits differ, here's an example #  7:  [a0 = hi, sel = lo, d1b = lo, d1a = dn]
# The mux circuits differ, here's an example #  8:  [a0 = hi, sel = lo, d1b = hi, d1a = g010]
# The mux circuits differ, here's an example #  9:  [a0 = hi, sel = lo, d1b = hi, d1a = dn]
# The mux circuits differ, here's an example # 10:  [a0 = hi, sel = lo, d1b = hi, d1a = up]
# The mux circuits differ, here's an example # 11:  [a0 = hi, sel = lo, d1b = hi, d1a = g101]
# The mux circuits differ, here's an example # 12:  [a0 = hi, sel = lo, d1b = dn, d1a = g010]
# The mux circuits differ, here's an example # 13:  [a0 = hi, sel = lo, d1b = g010, d1a = g010]
# The mux circuits differ, here's an example # 14:  [a0 = hi, sel = lo, d1b = up, d1a = g010]
# The mux circuits differ, here's an example # 15:  [a0 = hi, sel = lo, d1b = dn, d1a = hi]
# The mux circuits differ, here's an example # 16:  [a0 = hi, sel = lo, d1b = dn, d1a = dn]
# The mux circuits differ, here's an example # 17:  [a0 = hi, sel = lo, d1b = up, d1a = hi]
# The mux circuits differ, here's an example # 18:  [a0 = hi, sel = lo, d1b = g010, d1a = hi]
# The mux circuits differ, here's an example # 19:  [a0 = hi, sel = lo, d1b = g010, d1a = g101]
# The mux circuits differ, here's an example # 20:  [a0 = hi, sel = lo, d1b = X, d1a = hi]
# The mux circuits differ, here's an example # 21:  [a0 = hi, sel = lo, d1b = dn, d1a = g101]
# The mux circuits differ, here's an example # 22:  [a0 = hi, sel = lo, d1b = g101, d1a = hi]
# The mux circuits differ, here's an example # 23:  [a0 = hi, sel = lo, d1b = hi, d1a = X]
# The mux circuits differ, here's an example # 24:  [a0 = hi, sel = lo, d1b = up, d1a = g101]
# The mux circuits differ, here's an example # 25:  [a0 = hi, sel = lo, d1b = up, d1a = X]
# The mux circuits differ, here's an example # 26:  [a0 = hi, sel = lo, d1b = g010, d1a = X]
# The mux circuits differ, here's an example # 27:  [a0 = hi, sel = lo, d1b = dn, d1a = X]
# The mux circuits differ, here's an example # 28:  [a0 = hi, sel = lo, d1b = g101, d1a = g010]
# The mux circuits differ, here's an example # 29:  [a0 = hi, sel = lo, d1b = g101, d1a = g101]
# The mux circuits differ, here's an example # 30:  [a0 = hi, sel = lo, d1b = X, d1a = g010]
# The mux circuits differ, here's an example # 31:  [a0 = hi, sel = lo, d1b = X, d1a = X]
# The mux circuits differ, here's an example # 32:  [a0 = hi, sel = lo, d1b = g101, d1a = dn]
# The mux circuits differ, here's an example # 33:  [a0 = hi, sel = lo, d1b = g101, d1a = X]
# The mux circuits differ, here's an example # 34:  [a0 = hi, sel = lo, d1b = up, d1a = dn]
# The mux circuits differ, here's an example # 35:  [a0 = hi, sel = lo, d1b = dn, d1a = up]
# The mux circuits differ, here's an example # 36:  [a0 = hi, sel = lo, d1b = g101, d1a = up]
# The mux circuits differ, here's an example # 37:  [a0 = hi, sel = lo, d1b = X, d1a = up]
# The mux circuits differ, here's an example # 38:  [a0 = hi, sel = lo, d1b = X, d1a = g101]
# The mux circuits differ, here's an example # 39:  [a0 = hi, sel = lo, d1b = X, d1a = dn]
# The mux circuits differ, here's an example # 40:  [a0 = hi, sel = lo, d1b = up, d1a = up]
# We have found all 40 example cases where the muxes differ.
# 

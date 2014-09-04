# GlBool.py -- boolean values that include glitches and 'unknown'
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


from z3     import *
from string import split

# define GlBool and its possible values
GlBool = Datatype('BoolGl')
GlBool.declare('lo')
GlBool.declare('hi')
GlBool.declare('up')
GlBool.declare('dn')
GlBool.declare('g010')
GlBool.declare('g101')
GlBool.declare('X')
GlBool = GlBool.create()

# enable the definition of multiple GlBools (like the Z3 Bools() function)
def GlBools(names) :
  return [Const(who, GlBool) for who in split(names)]


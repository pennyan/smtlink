z3_interface README
=====================

Subdirectory z3_interface is for storing interface files to
SMT solvers.

The default z3 interface file provided is ACL2_to_Z3.py.

***  Basic functions

Smtlink's built-in translator requires several premitive
functions to be implemented. Below is the list of functions
needed:

  Option             | Explanation
  ------------------ | ---------------------------------
  __SMT__.plus       | binary addition
  __SMT__.times      | binary multiplication
  __SMT__.reciprocal | reciprocal
  __SMT__.negate     | numerical negation
  __SMT__.equal      | equality
  __SMT__.lt         | less than
  __SMT__.ifx        | if statement
  __SMT__.not        | logic negation
  lambda             | lambda expression
  __SMT__.implies    | logic implication
  __SMT__.hint_okay  | function that always return false
  __SMT__.isInt      | integer type
  __SMT__.isReal     | real type
  __SMT__.isBool     | boolean type

Check details in ACL2_to_Z3.py.

*** Customized module

Check details in RewriteExpt.py for extended module with customized abilities.

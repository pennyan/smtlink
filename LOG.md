
2016-09-27
=================================================================

The current status:
--------------------------

1. Example 1 in examples/examples.lisp is working. This means basic theorems should be fine.
2. Example 2 not working. Z3 returns "failed to prove". This is understandable because we are using uninterpreted functions with non-linear arithmetic.
3. Buggy example. Failed. Notice this buggy example fail with the error
message "Not a basic SMT function: INTEGERP". This is on purpose. Currently Smtlink does not support hyptheses about types that are not declarations. This is because of the mismatch of types between Z3 and ACL2.

What needs to be done:
--------------------------

1. The hint passing mechanism we discussed about. This should solve Example 2.
2. A way of automatically generating smtlink-hint and a way of easy adjusting.
3. Clean up theorems appeared in the code.
4. Possible optimization.
5. Separate default smtlink from customized smtlink
5. Any others?

What's done:
--------------------------

1. Added int-to-rat option.
2. Now all functions are symbols in package SMT.
3. Now the code is divided into two parts, verified and trusted. Verified use a verified clause processor to verify goal generation. Then a hint-wrapper looks for SMT goal and feed it to the trusted part.
4. py_utils are python scripts for configuration.
5. Nearly all functions are guard verified, except for some small amount of function that deals with the trusted clause processor.
6. Used defsection and defxdoc. Documents will be automatically generated after certification.


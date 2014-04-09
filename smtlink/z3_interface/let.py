import ACL2_2_Z3
smt = ACL2_2_Z3
foo = smt()

def v(name):
  return foo.getvar(name)

# assume that in ACL2 we had
# (defun funny (x y) (+ (* x x) (* y y)))
# (defun bunny (x y) (* (+ x y) (- x y)))
# (defun square (x) (* x x))
# 
# (defthm mythm
#   (implies (and (isnumber a) (isnumber b))
#     (equals
#       (- (square (funny a b)) (square (bunny a b)))
#       (* 4 a a b b)
#     )
#   )
#   :hint (my_smt (expand '( '(myfun rational rational) '(gt0 rational))))
# )
#
# I'll ignore the various rewrites that ACL2 does, and just expand
# my three functions.  The expanded claims is
# (implies (and (isnumber a) (isnumber b))
#   (equals
#     (- (let ('var1 (let (('var2 a) ('var3 b)) (+ (* var2 var2) (* var3 var3)))) (* var1 var1))
#        (let ('var4 (let (('var5 a) ('var6 b)) (* (+ var5 var6) (- var5 var6)))) (* var4 var4))
#     )
#     (* 4 a a b b)
#   )
# )

stuff.bind('a', acl2.RealSort())
stuff.bind('b', acl2.RealSort())
# a few test cases
# this one should be proven successfully.  It's equivalent to
# (equals (let ('var2 a) var2) a)
# stuff.claim(acl2.equals(stuff.bind('var2', v('a')).val(v('var2')),v('a')))

# this one should fail and print a counter-example.  It's equivalent to
# (equals (let ('var2 a) var2) b)
# stuff.claim(acl2.equals(stuff.bind('var2', v('a')).val(v('var2')),v('b')))


# Finally, the original claim
stuff.claim(acl2.equals(
  acl2.minus(
    stuff.bind('var1', stuff.bind('var2', v('a')).bind('var3', v('b')).val(
      acl2.plus(acl2.times(v('var2'), v('var2')), acl2.times(v('var3'), v('var3')))
    )).val(acl2.times(v('var1'), v('var1'))),
    stuff.bind('var4', stuff.bind('var5', v('a')).bind('var6', v('b')).val(
      acl2.times(acl2.plus(v('var5'), v('var6')), acl2.minus(v('var5'), v('var6')))
    )).val(acl2.times(v('var4'), v('var4')))
  ),
  acl2.times(4, v('a'), v('a'), v('b'), v('b'))
))

if(stuff.prove()):
  print "success!"
else:
  print "failure -- here's a counter-example:  " + stuff.cex()

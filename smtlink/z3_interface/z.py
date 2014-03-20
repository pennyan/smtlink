import z3x

aa = z3x.to_smt()

X=aa.isReal("X")
Y=aa.isReal("Y")
Z=aa.isReal("Z")
hyp = aa.ifx(aa.lt(-1,X),aa.gt(X,Y),False)
concl = aa.lt(aa.multiply(X,Y),aa.multiply(X,X))
x =  aa.prove(hyp, concl)
if(x.isThm()): print "It's a theorem!"
else: print "You're a bozo -- here's a counter-example to your supposed theorem:  ", str(x)

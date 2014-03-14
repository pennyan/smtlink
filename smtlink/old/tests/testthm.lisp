(in-package "ACL2")
(include-book "arithmetic/top-with-meta" :dir :system)#|ACL2s-ToDo-Line|#


(defthm simpleThm
    (implies (and (and (acl2-numberp x) (acl2-numberp y))
                  (and (and (not (<= x 0))) (> x y)))
             (> (simpleFun x y) 0)
    )
    :hints (("Goal"
             :do-not-induct t))
  )

;; The corresponding Z3 code should be like:
;; 
;; simpleConst = 1
;; x = Real("x")
;; y = Real("y")

;; def f3(): return 1
;; def f2(x): return x*x
;; def simpleFun (x,y) : return f2(x)*simpleConst-f3()*x*y

;; Conditions = And(True, x > 0, x > y)
;; Conclusions = simpleFun(x,y) > 0
;; prove(Implies(Conditions, Conclusions))
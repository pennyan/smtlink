(add-include-book-dir :cp "/ubc/cs/home/y/yanpeng/project/ACL2/smtlink")
(include-book "top" :dir :cp)
(tshell-ensure)

(defthm poly-ineq-example
    (implies (and (rationalp x) (rationalp y)
                  (<= (+ (* (/ 9 8) x x) (* y y)) 1)
                      (<= (- (* x x) (* y y)) 1))
	       (<= y (* 3 (- x (/ 17 8)) (- x (/ 17 8)))))
    :hints(("Goal"
      :clause-processor
      (Smtlink clause nil state))))


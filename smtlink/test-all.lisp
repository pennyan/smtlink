;; test cases

;; very first piece of test case
(thm (implies (and (and (rationalp x)
			(integerp y)
			(integerp z))
		   (and (not (<= x 0))
			(equal z (- 2 4))
			(or (> x y) (> x (+ y 1)))))
	      (> (* x x z) (* x y)))
     :hints
            (("Goal"
              :clause-processor
              (my-clause-processor clause "test1"))))

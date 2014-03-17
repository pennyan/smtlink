(thm (implies (and (and (rationalp x)
			(integerp y))
		   (and (> x 0)
			(equal z 1)
			(or (> x y) (> x (+ y 1)))))
	      (> (* x x z) (* x y)))
     :hints
            (("Goal"
              :clause-processor
              (my-clause-processor clause))))

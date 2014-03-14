(thm (implies (and (and (rationalp x)
			(integerp y))
		   (and (> x 0) (or (> x y) (> x (+ y 1)))))
	      (> (* x x) (* x y)))
     :hints
            (("Goal"
              :clause-processor
              (my-clause-processor clause '(equal a a)))))

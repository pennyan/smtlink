(thm
    (implies
     ( (lambda (expt_gamma_h expt_gamma_minus_h h)
		  (implies
		    (and  (rationalp expt_gamma_minus_h)
			  (rationalp expt_gamma_h)
			  (integerp h)
			  (equal expt_gamma_minus_h (/ expt_gamma_h))
			  (< '0 expt_gamma_h)
			  (< expt_gamma_h '1)
			  (not (< h '1))
		    )
		    (<
		      (+
			(* expt_gamma_h
			   ( (lambda (|var0|)
			       (+ '-1
				  (* (* '1 (/ (* '1 '1)))
				     (* (+ '1 (* '1 '1))
					(/ (+ '1 (* '1 (+ (* |var0| '1/3200) (+ (* (* '1 (/ (* '1 (* '1 '1)))) (+ '1 (* '1 '1))) (- (* '1 (/ '1))))))))
				     )))
			     ) h))
			(* expt_gamma_minus_h
			   ( (lambda (|var1|)
			       (+ '-1
				  (* (* '1 (/ (* '1 '1)))
				     (* (+ '1 (* '1 '1))
					(/ (+ '1 (* '1 (+ (* |var1| '1/3200) (+ (* (* '1 (/ (* '1 (* '1 '1)))) (+ '1 (* '1 '1))) (- (* '1 (/ '1))))))))
				     )))
			     ) (- h)))
		    )
		    '0)
		  ))
	   (b-term-expt h) (b-term-expt (- h)) h)
    (implies
      (if (integerp h) (not (< h '1)) 'nil)
      (<
	(+ (* (b-term-expt h) (b-term-rest h))
	   (* (b-term-expt (- h)) (b-term-rest (- h))))
	'0))
  )
)
;; Subgoal 1.3
(implies (not (integerp h))
         (< (+ (* 2 (/ (+ 2 (* 1/3200 h))))
               (* 2 (/ (+ 2 (- (* 1/3200 h))))))
            2))

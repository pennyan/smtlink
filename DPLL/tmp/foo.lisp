(in-package "ACL2")
(include-book "../global")
(include-book "../old_code/DPLL-functions")
(include-book "arithmetic/top-with-meta" :dir :system)

;; for the clause processor to work
(include-book "../../smtlink/SMT-connect")
(logic)
:set-state-ok t

(defun B-term-expt (h)
  (expt (gamma) (- h)))

(defun B-term-rest (h)
  (- (* (mu) (/ (+ 1 (* *alpha* *v0*)) (+ 1 (* *beta* (+ (* h *g1*) (equ-c)))))) 1))

(defun B-term (h) 
  (* (expt (gamma) (- h)) (- (* (mu) (/ (+ 1 (* *alpha* *v0*)) (+ 1 (* *beta* (+ (* h *g1*) (equ-c)))))) 1)))

(defun B-sum (h_lo h_hi)
  (declare (xargs :measure (if (or (not (integerp h_lo))
				   (not (integerp h_hi))
				   (< h_hi h_lo))
			       0
			       (1+ (- h_hi h_lo)))))
  (if (or (not (integerp h_hi)) (not (integerp h_lo)) (> h_lo h_hi))  0
      (+ (B-term h_hi) (B-term (- h_hi)) (B-sum h_lo (- h_hi 1)))))

(defun B-expt (n)
  (expt (gamma) (- n 2)))

(defun B (n)
  (* (expt (gamma) (- n 2))
     (B-sum 1 (- n 2))))

(encapsulate ()

(local
 (defthm B-term-neg-lemma1
     (equal (B-term h) (* (B-term-expt h) (B-term-rest h)))))

(local
 (defthm B-term-neg-lemma2
     (equal (B-term (- h)) (* (B-term-expt (- h)) (B-term-rest (- h))))))

(local
(defthm B-term-neg-lemma3
  (implies (and (integerp h) (>= h 1)) (< (+ (* (B-term-expt h) (B-term-rest h))
					     (* (B-term-expt (- h)) (B-term-rest (- h))))
					 0))
  :hints
  (("Goal"
    :clause-processor
    (my-clause-processor clause
			 '( (:expand (B-term-rest gamma mu equ-c))
			    (:python-file "B-term-neg") ;;mktemp
			    (:let ((expt_gamma_h (B-term-expt h) rationalp)
				   (expt_gamma_minus_h (B-term-expt (- h)) rationalp)))
			    (:hypothesize ((> expt_gamma_h 1)
					   (equal expt_gamma_minus_h (/ expt_gamma_h))))))
    )))
)

(defthm B-term-neg
  (implies (and (integerp h) (>= h 1)) (< (+ (B-term h) (B-term (- h))) 0))
  :hints (("Goal"
	   :use ((:instance B-term-neg-lemma1)
		 (:instance B-term-neg-lemma2)
		 (:instance B-term-neg-lemma3))))
  :rule-classes :linear)
)

(defthm B-sum-neg
  (implies (and (integerp n-minus-2) (>= n-minus-2 1)) (< (B-sum 1 n-minus-2) 0))
  :hints (("Goal"
	   :in-theory (disable B-term)))
  :rule-classes :linear)

(encapsulate ()
	     
(local ;; B = B-expt*B-sum
 (defthm B-neg-lemma1
   (implies (and (integerp n) (> n 2))
	    (equal (B n) (* (B-expt n)
			    (B-sum 1 (- n 2)))))))
(local
 (defthm B-expt->-0
   (implies (and (integerp n) (> n 2)) (> (B-expt n) 0))
   :rule-classes :linear))

(local
 (defthm B-neg-lemma2
   (implies (and (rationalp a)
		 (rationalp b)
		 (> a 0)
		 (< b 0))
	    (< (* a b) 0))
   :rule-classes :linear))

(local
 (defthm B-neg-type-lemma3
   (implies (and (integerp n-minus-2) (>= n-minus-2 1))
	    (rationalp (B-sum 1 n-minus-2)))
   :rule-classes :type-prescription))

(local
 (defthm B-neg-type-lemma4
   (implies (and (integerp n) (> n 2))
	    (rationalp (B-expt n)))
   :rule-classes :type-prescription))

(defthm B-neg
  (implies (and (integerp n) (> n 2)) (< (B n) 0))
  :hints (("Goal"
	   :do-not-induct t
	   :in-theory (disable B-expt B-sum B-sum-neg B-expt->-0)
	   :use ((:instance B-sum-neg (n-minus-2 (- n 2)))
		 (:instance B-expt->-0)
		 (:instance B-neg-type-lemma3 (n-minus-2 (- n 2)))
		 (:instance B-neg-type-lemma4)
		 (:instance B-neg-lemma2 (a (B-expt n))
			                 (b (B-sum 1 (+ -2 n))))))))
)

(in-package "ACL2")
(include-book "global")
(include-book "arithmetic/top-with-meta" :dir :system)

;; for the clause processor to work
(include-book "../smtlink/SMT-connect")
(logic)
:set-state-ok t
:set-ignore-ok t

;; functions
(defun fdco (n v0 dv g1)
  (/ (* (mu) (+ 1 (* *alpha* (+ v0 dv)))) (+ 1 (* *beta* n g1))))

(defun B-term-expt (h)
  (expt (gamma) (- h)))

(defun B-term-rest (h v0 dv g1)
  (- (* (mu) (/ (+ 1 (* *alpha* (+ v0 dv))) (+ 1 (* *beta* (+ (* h g1) (equ-c)))))) 1))

(defun B-term (h v0 dv g1)
  (* (B-term-expt h) (B-term-rest h v0 dv g1)))

(defun B-sum (h_lo h_hi v0 dv g1)
  (declare (xargs :measure (if (or (not (integerp h_lo))
				   (not (integerp h_hi))
				   (< h_hi h_lo))
			       0
			       (1+ (- h_hi h_lo)))))
  (if (or (not (integerp h_hi)) (not (integerp h_lo)) (> h_lo h_hi))  0
      (+ (B-term h_hi v0 dv g1) (B-term (- h_hi) v0 dv g1) (B-sum h_lo (- h_hi 1) v0 dv g1))))

(defun B-expt (n)
  (expt (gamma) (- n 2)))

(defun B (n v0 dv g1)
  (* (B-expt n)
     (B-sum 1 (- n 2) v0 dv g1)))

;; parameter list functions
(defmacro basic-params-equal (n n-value &optional (v0 'nil) (dv 'nil) (g1 'nil) (phi0 'nil) (n-4-phi0 'nil) (other 'nil))
  (list 'and
	(append
	 (append
	  (append
	   (append (list 'and
			 (list 'rationalp n))
		   (if (equal g1 'nil) nil (list (list 'rationalp g1))))
	   (if (equal v0 'nil) nil (list (list 'rationalp v0))))
	  (if (equal phi0 'nil) nil (list (list 'rationalp phi0))))
	 (if (equal dv 'nil) nil (list (list 'rationalp dv))))
	(append
	 (append
	  (append
	   (append
	    (append
	     (append
	      (append
	       (append (list 'and
			     (list 'equal n n-value))
		       (if (equal g1 'nil) nil (list (list 'equal g1 '1/3200))))
	       (if (equal v0 'nil) nil (list (list '>= v0 '9/10))))
	      (if (equal v0 'nil) nil (list (list '<= v0 '11/10))))
	     (if (equal dv 'nil) nil (list (list '>= dv (list '- (list 'dv0))))))
	    (if (equal dv 'nil) nil (list (list '<= dv (list 'dv0)))))
	   (if (equal phi0 'nil) nil (list (list '>= phi0 '0))))
	  (if (equal phi0 'nil) nil (list (list '< phi0 (list '- (list 'fdco (list '1+ (list 'm n-4-phi0 g1)) v0 dv g1) '1)))))
	 (if (equal other 'nil) nil (list other)))))

(defmacro basic-params (n n-value &optional (v0 'nil) (dv 'nil) (g1 'nil) (phi0 'nil) (n-4-phi0 'nil) (other 'nil))
  (list 'and
	(append
	 (append
	  (append
	   (append (list 'and
			 (list 'rationalp n))
		   (if (equal g1 'nil) nil (list (list 'rationalp g1))))
	   (if (equal v0 'nil) nil (list (list 'rationalp v0))))
	  (if (equal dv 'nil) nil (list (list 'rationalp dv))))
	 (if (equal phi0 'nil) nil (list (list 'rationalp phi0))))
	(append
	 (append
	  (append
	   (append
	    (append
	     (append
	      (append
	       (append (list 'and
			     (list '>= n n-value))
		       (if (equal g1 'nil) nil (list (list 'equal g1 '1/3200))))
	       (if (equal v0 'nil) nil (list (list '>= v0 '9/10))))
	      (if (equal v0 'nil) nil (list (list '<= v0 '11/10))))
	     (if (equal dv 'nil) nil (list (list '>= dv (list '- (list 'dv0))))))
	    (if (equal dv 'nil) nil (list (list '<= dv (list 'dv0)))))
	   (if (equal phi0 'nil) nil (list (list '>= phi0 '0))))
	  (if (equal phi0 'nil) nil (list (list '< phi0 (list '- (list 'fdco (list '1+ (list 'm n-4-phi0 g1)) v0 dv g1) '1)))))
	 (if (equal other 'nil) nil (list other)))))

;; (encapsulate
;;   ( ((my-floor *) => *) )
;;   (local (defun my-floor (x) (floor (denominator x) (numerator x))))
;;   (defthm type
;;      (implies (rationalp x)
;; 	      (integerp (my-floor x))))
;;   (defthm range
;;      (implies (and (>= x 0)
;; 		   (rationalp x))
;; 	      (and (>= (my-floor x) (- x 1))
;; 		   (<= (my-floor x) x)))))

(defun my-floor (x) (floor (numerator x) (denominator x)))

(defthm my-floor-type
  (implies (rationalp x)
	   (integerp (my-floor x)))
  :rule-classes :type-prescription)

(encapsulate ()

(local
(defthm B-term-neg-lemma1
  (implies (basic-params h 1 v0 dv g1)
	   (< (+ (* (B-term-expt (my-floor h)) (B-term-rest (my-floor h) v0 dv g1))
		 (* (B-term-expt (- (my-floor h))) (B-term-rest (- (my-floor h)) v0 dv g1)))
	      0))
  :hints
  (("Goal"
    :in-theory (disable floor my-floor)
    :clause-processor
    (my-clause-processor clause
			 '( (:expand ((:functions ((B-term-rest rationalp)
						   (gamma rationalp)
						   (mu rationalp)
						   (equ-c rationalp)
						   (dv0 rationalp)))
				      (:expansion-level 1)))
			    (:python-file "B-term-neg-lemma3") ;;mktemp
			    (:let ((expt_gamma_h (B-term-expt (my-floor h)) rationalp)
				   (expt_gamma_minus_h (B-term-expt (- (my-floor h))) rationalp)))
			    (:hypothesize ((> expt_gamma_h 1)
					   (equal expt_gamma_minus_h (/ expt_gamma_h))))))
    )))
)

(defthm B-term-neg
  (implies (basic-params h 1 v0 dv g1)
	   (< (+ (B-term (my-floor h) v0 dv g1) (B-term (- (my-floor h)) v0 dv g1)) 0))
  :hints (("Goal"
	   :use ( (:instance B-term)
		 (:instance B-term-neg-lemma1))))
  :rule-classes :linear)
)

(defthm B-sum-neg
  (implies (basic-params n-minus-2 1 v0 dv g1)
	   (< (B-sum 1 (my-floor n-minus-2) v0 dv g1) 0))
  :hints (("Goal"
	   :in-theory (disable B-term)))
  :rule-classes :linear)

(encapsulate ()
	     
(local ;; B = B-expt*B-sum
 (defthm B-neg-lemma1
   (implies (basic-params n 3 v0 dv g1)
	    (equal (B (my-floor n) v0 dv g1)
		   (* (B-expt (my-floor n))
		      (B-sum 1 (- (my-floor n) 2) v0 dv g1))))))

(local
 (defthm B-expt->-0
   (implies (basic-params n 3)
	    (> (B-expt (my-floor n)) 0))
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
 (defthm B-neg-type-lemma3-lemma1
   (implies (and (and (integerp n-minus-2) (rationalp v0) (rationalp g1) (rationalp dv)))
	    (rationalp (B-sum 1 n-minus-2 v0 dv g1)))
   :rule-classes :type-prescription))

(local
 (defthm B-neg-type-lemma3
   (implies (and (and (rationalp n-minus-2) (rationalp v0) (rationalp g1) (rationalp dv)))
	    (rationalp (B-sum 1 (my-floor n-minus-2) v0 dv g1)))
   :hints (("Goal"
   	    :use ((:instance B-neg-type-lemma3-lemma1 (n-minus-2 (my-floor n-minus-2)))
		  (:instance my-floor-type (x n-minus-2)))))
   :rule-classes :type-prescription))

(local
 (defthm B-neg-type-lemma4
   (implies (basic-params n 3)
	    (rationalp (B-expt (my-floor n))))
   :rule-classes :type-prescription))

(defthm B-neg
  (implies (basic-params n 3 v0 dv g1)
	   (< (B (my-floor n) v0 dv g1) 0))
  :hints (("Goal"
	   :do-not-induct t
	   :in-theory (disable B-expt B-sum B-sum-neg B-expt->-0)
	   :use ((:instance B-sum-neg (n-minus-2 (- n 2)))
		 (:instance B-expt->-0)
		 (:instance B-neg-type-lemma3 (n-minus-2 (- n 2)))
		 (:instance B-neg-type-lemma4)
		 (:instance B-neg-lemma2 (a (B-expt n))
			                 (b (B-sum 1 (+ -2 n) v0 dv g1)))))))
)

(defun A (n phi0 v0 dv g1)
  (+ (* (expt (gamma) (- (* 2 n) 1)) phi0)
     (* (expt (gamma) (- (* 2 n) 2))
	(- (fdco (m n g1) v0 dv g1) 1))
     (* (expt (gamma) (- (* 2 n) 3))
	(- (fdco (1+ (m n g1)) v0 dv g1) 1))))

(defun phi-2n-1 (n phi0 v0 dv g1)
  (+ (A n phi0 v0 dv g1) (B n v0 dv g1)))

(defun delta (n v0 dv g1)
  (+ (- (* (expt (gamma) (* 2 n))
	   (- (fdco (1- (m n g1)) v0 dv g1) 1))
	(* (expt (gamma) (* 2 n)) 
	   (- (fdco (m n g1) v0 dv g1) 1)))
     (- (* (expt (gamma) (- (* 2 n) 1))
	   (- (fdco (m n g1) v0 dv g1) 1))
	(* (expt (gamma) (- (* 2 n) 1))
	   (- (fdco (1+ (m n g1)) v0 dv g1) 1)))
     (* (expt (gamma) (1- n))
	(+ (* (expt (gamma) (1+ (- n)))
	      (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
		    (1+ (* *beta* (+ (* g1 (1- n)) (equ-c)))))
		 1))
	   (* (expt (gamma) (1- n))
	      (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
		    (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c)))))
		 1))))))

(defun delta-1 (n v0 dv g1)
  (+ (* (expt (gamma) (* 2 n))
	(- (fdco (1- (m n g1)) v0 dv g1)
	   (fdco (m n g1) v0 dv g1)))
     (* (expt (gamma) (- (* 2 n) 1))
	(- (fdco (m n g1) v0 dv g1)
	   (fdco (1+ (m n g1)) v0 dv g1)))
     (* (* (expt (gamma) (1- n)) (expt (gamma) (1+ (- n))))
	(- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
	      (1+ (* *beta* (+ (* g1 (1- n)) (equ-c))))) 1))
     (* (* (expt (gamma) (1- n)) (expt (gamma) (1- n)))
	(- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
	      (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c))))) 1))))

(defun delta-2 (n v0 dv g1)
  (+ (* (expt (gamma) (* 2 n))
	(- (fdco (1- (m n g1)) v0 dv g1)
	   (fdco (m n g1) v0 dv g1)))
     (* (expt (gamma) (- (* 2 n) 1))
	(- (fdco (m n g1) v0 dv g1)
	   (fdco (1+ (m n g1)) v0 dv g1)))
     (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
	   (1+ (* *beta* (+ (* g1 (1- n)) (equ-c))))) 1)
     (* (expt (gamma) (+ -1 n -1 n))
	(- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
	      (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c))))) 1))))

(defun delta-3 (n v0 dv g1)
  (* (expt (gamma) (+ -1 n -1 n))
     (+ (* (expt (gamma) 2)
	   (- (fdco (1- (m n g1)) v0 dv g1)
	      (fdco (m n g1) v0 dv g1)))
	(* (expt (gamma) 1)
	   (- (fdco (m n g1) v0 dv g1)
	      (fdco (1+ (m n g1)) v0 dv g1)))
	(* (expt (gamma) (- 2 (* 2 n)))
	   (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
		 (1+ (* *beta* (+ (* g1 (1- n)) (equ-c))))) 1))
	(- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
	      (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c))))) 1))))

(defun delta-3-inside (n v0 dv g1)
  (+ (* (expt (gamma) 2)
	   (- (fdco (1- (m n g1)) v0 dv g1)
	      (fdco (m n g1) v0 dv g1)))
	(* (expt (gamma) 1)
	   (- (fdco (m n g1) v0 dv g1)
	      (fdco (1+ (m n g1)) v0 dv g1)))
	(* (expt (gamma) (- 2 (* 2 n)))
	   (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
		 (1+ (* *beta* (+ (* g1 (1- n)) (equ-c))))) 1))
	(- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
	      (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c))))) 1)))

(defun delta-3-inside-transform (n v0 dv g1)
  (/ 
   (+ (* (expt (gamma) 2)
	 (- (fdco (1- (m n g1)) v0 dv g1)
	    (fdco (m n g1) v0 dv g1)))
      (* (expt (gamma) 1)
	 (- (fdco (m n g1) v0 dv g1)
	    (fdco (1+ (m n g1)) v0 dv g1)))
      (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
	    (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c))))) 1))
   (- 1
      (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
	 (1+ (* *beta* (+ (* g1 (1- n)) (equ-c))))))))

;; rewrite delta term
(encapsulate ()

(local
;; considering using smtlink for the proof, probably simpler
(defthm delta-rewrite-1-lemma1
  (implies (basic-params n 3 v0 dv g1)
	   (equal (+ (- (* (expt (gamma) (* 2 (my-floor n)))
			   (- (fdco (1- (m (my-floor n) g1)) v0 dv g1) 1))
			(* (expt (gamma) (* 2(my-floor n)))
			   (- (fdco (m (my-floor n) g1) v0 dv g1) 1)))
		     (- (* (expt (gamma) (- (* 2 (my-floor n)) 1))
			   (- (fdco (m (my-floor n) g1) v0 dv g1) 1))
			(* (expt (gamma) (- (* 2 (my-floor n)) 1))
			   (- (fdco (1+ (m (my-floor n) g1)) v0 dv g1) 1)))
		     (* (expt (gamma) (1- (my-floor n)))
			(+ (* (expt (gamma) (1+ (- (my-floor n))))
			      (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				    (1+ (* *beta* (+ (* g1 (1- (my-floor n))) (equ-c)))))
				 1))
			   (* (expt (gamma) (1- (my-floor n)))
			      (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				    (1+ (* *beta* (+ (* g1 (- 1 (my-floor n))) (equ-c)))))
				 1)))))
		    (+ (* (expt (gamma) (* 2 (my-floor n)))
			  (- (fdco (1- (m (my-floor n) g1)) v0 dv g1)
			     (fdco (m (my-floor n) g1) v0 dv g1)))
		       (* (expt (gamma) (- (* 2 (my-floor n)) 1))
			  (- (fdco (m (my-floor n) g1) v0 dv g1)
			     (fdco (1+ (m (my-floor n) g1)) v0 dv g1)))
		       (* (* (expt (gamma) (1- (my-floor n))) (expt (gamma) (1+ (- (my-floor n)))))
			  (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				(1+ (* *beta* (+ (* g1 (1- (my-floor n))) (equ-c))))) 1))
		       (* (* (expt (gamma) (1- (my-floor n))) (expt (gamma) (1- (my-floor n))))
			  (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				(1+ (* *beta* (+ (* g1 (- 1 (my-floor n))) (equ-c))))) 1)))))
  :hints
  (("Goal"
    :clause-processor
    (my-clause-processor clause
			 '( (:expand ((:functions ((m integerp)
						   (gamma rationalp)
						   (mu rationalp)
						   (equ-c rationalp)
						   (fdco rationalp)
						   (dv0 rationalp)))
				      (:expansion-level 1)))
			    (:python-file "delta-rewrite-1-lemma1") ;;mktemp
			    (:let ((expt_gamma_2n
				    (expt (gamma) (* 2 (my-floor n)))
				     rationalp)
				   (expt_gamma_2n_minus_1
				    (expt (gamma) (- (* 2 (my-floor n)) 1))
				     rationalp)
				   (expt_gamma_n_minus_1
				    (expt (gamma) (1- (my-floor n)))
				     rationalp)
				   (expt_gamma_1_minus_n
				    (expt (gamma) (1+ (- (my-floor n))))
				     rationalp)
				   ))
			    (:hypothesize ())))
    )))
)

(local
(defthm delta-rewrite-1
  (implies (basic-params n 3 v0 dv g1)
	   (equal (delta (my-floor n) v0 dv g1)
		  (delta-1 (my-floor n) v0 dv g1))))
)

(local
(defthm delta-rewrite-2-lemma1
  (implies (basic-params n 3)
	   (equal (* (expt (gamma) (1- (my-floor n)))
		     (expt (gamma) (1+ (- (my-floor n)))))
		  1))
  :hints (("Goal"
	   :use ((:instance expt-minus
			    (r (gamma))
			    (i (- (1+ (- (my-floor n))))))))))
)

(local
(defthm delta-rewrite-2-lemma2
  (implies (basic-params n 3)
 	   (equal (* (expt (gamma) (1- (my-floor n)))
 		     (expt (gamma) (1- (my-floor n))))
		  (expt (gamma) (+ -1 (my-floor n) -1 (my-floor n)))))
  :hints (("Goal"
	   :do-not-induct t
	   :use ((:instance exponents-add-for-nonneg-exponents
			    (i (1- (my-floor n)))
			    (j (1- (my-floor n)))
			    (r (gamma))))
	   :in-theory (disable exponents-add-for-nonneg-exponents))))
)

(local
(defthm delta-rewrite-2-lemma3
  (implies (basic-params n 3)
	   (equal (+ A
		     B
		     (* (* (expt (gamma) (1- (my-floor n)))
			   (expt (gamma) (1+ (- (my-floor n)))))
			C)
		     (* (* (expt (gamma) (1- (my-floor n)))
			   (expt (gamma) (1- (my-floor n))))
			D))
		  (+ A B C
		     (* (expt (gamma) (+ -1 (my-floor n) -1(my-floor n))) D))))
  :hints (("Goal"
	   :use ((:instance delta-rewrite-2-lemma1)
		 (:instance delta-rewrite-2-lemma2)))))
)

(local
(defthm delta-rewrite-2
  (implies (basic-params n 3 v0 dv g1)
	   (equal (delta-1 (my-floor n) v0 dv g1)
		  (delta-2 (my-floor n) v0 dv g1)))
  :hints (("Goal"
	   :use ((:instance delta-rewrite-2-lemma3
			    (A (* (expt (gamma) (* 2 (my-floor n)))
				  (- (fdco (1- (m (my-floor n) g1)) v0 dv g1)
				     (fdco (m (my-floor n) g1) v0 dv g1))))
			    (B (* (expt (gamma) (- (* 2 (my-floor n)) 1))
				  (- (fdco (m (my-floor n) g1) v0 dv g1)
				     (fdco (1+ (m (my-floor n) g1)) v0 dv g1))))
			    (C (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				     (1+ (* *beta* (+ (* g1 (1- (my-floor n))) (equ-c))))) 1))
			    (D (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				     (1+ (* *beta* (+ (* g1 (- 1 (my-floor n))) (equ-c))))) 1)))))))
)

(local
(defthm delta-rewrite-3-lemma1-lemma1
  (implies (basic-params n 3)
	   (equal (expt (gamma) (+ (+ -1 (my-floor n) -1 (my-floor n)) 2))
		  (* (expt (gamma) (+ -1 (my-floor n) -1 (my-floor n)))
		     (expt (gamma) 2))))
  :hints (("Goal"
	   :use ((:instance exponents-add-for-nonneg-exponents
			    (i (+ -1 (my-floor n) -1(my-floor n)))
			    (j 2)
			    (r (gamma))))
	   :in-theory (disable exponents-add-for-nonneg-exponents
			       delta-rewrite-2-lemma2))))
)

(local
(defthm delta-rewrite-3-lemma1-stupidlemma
  (implies (basic-params n 3)
	   (equal (* 2 (my-floor n)) (+ (+ -1 (my-floor n) -1 (my-floor n)) 2))))
)

(local
(defthm delta-rewrite-3-lemma1
  (implies (basic-params n 3)
	   (equal (expt (gamma) (* 2 (my-floor n)))
		  (* (expt (gamma) (+ -1 (my-floor n) -1 (my-floor n)))
		     (expt (gamma) 2))))
  :hints (("Goal"
	   :use ((:instance delta-rewrite-3-lemma1-lemma1)
		 (:instance delta-rewrite-3-lemma1-stupidlemma)))))
)

(local
(defthm delta-rewrite-3-lemma2-lemma1
  (implies (basic-params n 3)
	   (equal (expt (gamma) (+ (+ -1 (my-floor n) -1 (my-floor n)) 1))
		  (* (expt (gamma) (+ -1 (my-floor n) -1 (my-floor n)))
		     (expt (gamma) 1))))
  :hints (("Goal"
	   :do-not '(simplify)
	   :do-not-induct t
	   :use ((:instance exponents-add-for-nonneg-exponents
			    (i (+ -1 (my-floor n) -1 (my-floor n)))
			    (j 1)
			    (r (gamma))))
	   :in-theory (disable exponents-add-for-nonneg-exponents
			       delta-rewrite-2-lemma2))))
)

(local
(defthm delta-rewrite-3-lemma2-stupidlemma
  (implies (basic-params n 3)
	   (equal (- (* 2 (my-floor n)) 1) (+ (+ -1 (my-floor n) -1 (my-floor n)) 1))))
)

(local
(defthm delta-rewrite-3-lemma2
  (implies (basic-params n 3)
	   (equal (expt (gamma) (- (* 2 (my-floor n)) 1))
		  (* (expt (gamma) (+ -1 (my-floor n) -1 (my-floor n)))
		     (expt (gamma) 1))))
  :hints (("Goal"
	   :use ((:instance delta-rewrite-3-lemma2-lemma1)
		 (:instance delta-rewrite-3-lemma2-stupidlemma))
	   :in-theory (disable delta-rewrite-2-lemma1))))
)

(local
(defthm delta-rewrite-3-lemma3
  (implies (basic-params n 3)
	   (equal (* (expt (gamma) (- 2 (* 2 (my-floor n))))
		     (expt (gamma) (+ -1 (my-floor n) -1 (my-floor n))))
		  1))
  :hints (("Goal"
	   :use ((:instance expt-minus
			    (r (gamma))
			    (i (- (- 2 (* 2 (my-floor n))))))))))
)

(local
(defthm delta-rewrite-3
  (implies (basic-params n 3 v0 dv g1)
	   (equal (+ (* (expt (gamma) (* 2 (my-floor n)))
			(- (fdco (1- (m (my-floor n) g1)) v0 dv g1)
			   (fdco (m (my-floor n) g1) v0 dv g1)))
		     (* (expt (gamma) (- (* 2 (my-floor n)) 1))
			(- (fdco (m (my-floor n) g1) v0 dv g1)
			   (fdco (1+ (m (my-floor n) g1)) v0 dv g1)))
		     (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
			   (1+ (* *beta* (+ (* g1 (1- (my-floor n))) (equ-c))))) 1)
		     (* (expt (gamma) (+ -1 (my-floor n) -1 (my-floor n)))
			(- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
			      (1+ (* *beta* (+ (* g1 (- 1 (my-floor n))) (equ-c))))) 1)))
		  (* (expt (gamma) (+ -1 (my-floor n) -1 (my-floor n)))
		     (+ (* (expt (gamma) 2)
			   (- (fdco (1- (m (my-floor n) g1)) v0 dv g1)
			      (fdco (m (my-floor n) g1) v0 dv g1)))
			(* (expt (gamma) 1)
			   (- (fdco (m (my-floor n) g1) v0 dv g1)
			      (fdco (1+ (m (my-floor n) g1)) v0 dv g1)))
			(* (expt (gamma) (- 2 (* 2 (my-floor n))))
			   (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				 (1+ (* *beta* (+ (* g1 (1- (my-floor n))) (equ-c))))) 1))
			(- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
			      (1+ (* *beta* (+ (* g1 (- 1 (my-floor n))) (equ-c))))) 1)))))
  :hints
  (("Goal"
    :in-theory (disable delta-rewrite-2-lemma1)
    :do-not-induct t
    :clause-processor
    (my-clause-processor clause
			 '( (:expand ((:functions ((m integerp)
						   (gamma rationalp)
						   (mu rationalp)
						   (equ-c rationalp)
						   (fdco rationalp)
						   (dv0 rationalp)))
				      (:expansion-level 1)))
			    (:python-file "delta-rewrite-3")
			    (:let ((expt_gamma_2n
				    (expt (gamma) (* 2 (my-floor n)))
				     rationalp)
				   (expt_gamma_2n_minus_1
				    (expt (gamma) (- (* 2 (my-floor n)) 1))
				     rationalp)
				   (expt_gamma_2n_minus_2
				    (expt (gamma) (+ -1 (my-floor n) -1 (my-floor n)))
				     rationalp)
				   (expt_gamma_2
				    (expt (gamma) 2)
				     rationalp)
				   (expt_gamma_1
				    (expt (gamma) 1)
				     rationalp)
				   (expt_gamma_2_minus_2n
				    (expt (gamma) (- 2 (* 2 (my-floor n))))
				     rationalp)
				   ))
			    (:hypothesize ((equal expt_gamma_2n
					  	  (* expt_gamma_2n_minus_2 expt_gamma_2))
					   (equal expt_gamma_2n_minus_1
					  	  (* expt_gamma_2n_minus_2 expt_gamma_1))
					   (equal (* expt_gamma_2_minus_2n expt_gamma_2n_minus_2)
						  1)))
			    (:use ((:type ())
				   (:hypo ((delta-rewrite-3-lemma1)
					   (delta-rewrite-3-lemma2)
					   (delta-rewrite-3-lemma3)))
				   (:main ()))))))))
)

(local
(defthm delta-rewrite-4
  (implies (basic-params n 3 v0 dv g1)
	   (equal (delta-2 (my-floor n) v0 dv g1)
		  (delta-3 (my-floor n) v0 dv g1)))
  :hints (("Goal"
	   :use ((:instance delta-rewrite-3)))))
)

(defthm delta-rewrite-5
  (implies (basic-params n 3 v0 dv g1)
	   (equal (delta (my-floor n) v0 dv g1)
		  (delta-3 (my-floor n) v0 dv g1)))
  :hints (("Goal"
	   :use ((:instance delta-rewrite-1)
		 (:instance delta-rewrite-2)
		 (:instance delta-rewrite-3)
		 (:instance delta-rewrite-4)))))
)

(encapsulate ()

(local
(defthm delta-<-0-lemma1-lemma
  (implies (basic-params n 3 v0 dv g1)
	   (implies (< (+ (* (expt (gamma) 2)
			     (- (fdco (1- (m n g1)) v0 dv g1)
				(fdco (m n g1) v0 dv g1)))
			  (* (expt (gamma) 1)
			     (- (fdco (m n g1) v0 dv g1)
				(fdco (1+ (m n g1)) v0 dv g1)))
			  (* (expt (gamma) (- 2 (* 2 n)))
			     (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				   (1+ (* *beta* (+ (* g1 (1- n)) (equ-c))))) 1))
			  (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				(1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c))))) 1))
		       0)
		    (< (* (expt (gamma) (+ -1 n -1 n))
			  (+ (* (expt (gamma) 2)
				(- (fdco (1- (m n g1)) v0 dv g1)
				   (fdco (m n g1) v0 dv g1)))
			     (* (expt (gamma) 1)
				(- (fdco (m n g1) v0 dv g1)
				   (fdco (1+ (m n g1)) v0 dv g1)))
			     (* (expt (gamma) (- 2 (* 2 n)))
				(- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				      (1+ (* *beta* (+ (* g1 (1- n)) (equ-c))))) 1))
			     (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				   (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c))))) 1)))
		       0)))
  :hints (("Goal"
	   :clause-processor
	   (my-clause-processor clause
				'( (:expand ((:functions ((m integerp)
							  (gamma rationalp)
							  (mu rationalp)
							  (equ-c rationalp)
							  (fdco rationalp)
							  (dv0 rationalp)))
					     (:expansion-level 1)))
				  (:python-file "delta-smaller-than-0-lemma1-lemma")
				  (:let ((expt_gamma_2n
					  (expt (gamma) (* 2 n))
					   rationalp)
					 (expt_gamma_2n_minus_1
					  (expt (gamma) (- (* 2 n) 1))
					   rationalp)
					 (expt_gamma_2n_minus_2
					  (expt (gamma) (+ -1 n -1 n))
					   rationalp)
					 (expt_gamma_2
					  (expt (gamma) 2)
					   rationalp)
					 (expt_gamma_1
					  (expt (gamma) 1)
					   rationalp)
					 (expt_gamma_2_minus_2n
					  (expt (gamma) (- 2 (* 2 n)))
					   rationalp)
					 ))
				  (:hypothesize ((> expt_gamma_2n_minus_2 0))))))))
)

(local
(defthm delta-<-0-lemma1
  (implies (basic-params n 3 v0 dv g1)
	   (implies (< (delta-3-inside n v0 dv g1) 0)
		    (< (delta-3 n v0 dv g1) 0))))
)

(local
(defthm delta-<-0-lemma2-lemma
  (implies (basic-params n 3 v0 dv g1)
	   (implies (< (/ (+ (* (expt (gamma) 2)
				(- (fdco (1- (m n g1)) v0 dv g1)
				   (fdco (m n g1) v0 dv g1)))
			     (* (expt (gamma) 1)
				(- (fdco (m n g1) v0 dv g1)
				   (fdco (1+ (m n g1)) v0 dv g1)))
			     (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				   (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c))))) 1))
			  (- 1
			     (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				(1+ (* *beta* (+ (* g1 (1- n)) (equ-c)))))))
		       (expt (gamma) (- 2 (* 2 n))))
		    (< (+ (* (expt (gamma) 2)
			     (- (fdco (1- (m n g1)) v0 dv g1)
				(fdco (m n g1) v0 dv g1)))
			  (* (expt (gamma) 1)
			     (- (fdco (m n g1) v0 dv g1)
				(fdco (1+ (m n g1)) v0 dv g1)))
			  (* (expt (gamma) (- 2 (* 2 n)))
			     (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				   (1+ (* *beta* (+ (* g1 (1- n)) (equ-c))))) 1))
			  (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				(1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c))))) 1))
		       0)))
  :hints (("Goal"
	   :clause-processor
	   (my-clause-processor clause
				'( (:expand ((:functions ((m integerp)
							  (gamma rationalp)
							  (mu rationalp)
							  (equ-c rationalp)
							  (fdco rationalp)
							  (dv0 rationalp)))
					     (:expansion-level 1)))
				  (:python-file "delta-smaller-than-0-lemma2-lemma")
				  (:let ((expt_gamma_2n
					  (expt (gamma) (* 2 n))
					   rationalp)
					 (expt_gamma_2n_minus_1
					  (expt (gamma) (- (* 2 n) 1))
					   rationalp)
					 (expt_gamma_2n_minus_2
					  (expt (gamma) (+ -1 n -1 n))
					   rationalp)
					 (expt_gamma_2
					  (expt (gamma) 2)
					   rationalp)
					 (expt_gamma_1
					  (expt (gamma) 1)
					   rationalp)
					 (expt_gamma_2_minus_2n
					  (expt (gamma) (- 2 (* 2 n)))
					   rationalp)
					 ))
				  (:hypothesize ((> expt_gamma_2_minus_2n 0))))))))
)

(local
(defthm delta-<-0-lemma2
  (implies (basic-params n 3 v0 dv g1)
	   (implies (< (delta-3-inside-transform n v0 dv g1)
		       (expt (gamma) (- 2 (* 2 n))))
		    (< (delta-3-inside n v0 dv g1) 0)))
  :hints (("Goal"
	   :use ((:instance delta-<-0-lemma2-lemma)))))
)

(local
;; This is for proving 2n < gamma^(2-2n)
(defthm delta-<-0-lemma3-lemma1
  (implies (basic-params k 6)
	   (< k (expt (/ (gamma)) (- k 2)))))
)

(local
(defthm delta-<-0-lemma3-lemma2
  (implies (basic-params n 3)
	   (< (* 2 n)
	      (expt (/ (gamma)) (- (* 2 n) 2))))
  :hints (("Goal"
	   :use ((:instance delta-<-0-lemma3-lemma1
			   (k (* 2 n))))))
  :rule-classes :linear)
)

(local
(defthm delta-<-0-lemma3-lemma3-stupidlemma
  (equal (expt a n) (expt (/ a) (- n))))
)

(local
(defthm delta-<-0-lemma3-lemma3
  (implies (basic-params n 3)
	   (equal (expt (/ (gamma)) (- (* 2 n) 2))
		  (expt (gamma) (- 2 (* 2 n)))))
  :hints (("Goal"
	   :use ((:instance delta-<-0-lemma3-lemma3-stupidlemma
			    (a (/ (gamma)))
			    (n (- (* 2 n) 2))))
	   :in-theory (disable delta-<-0-lemma3-lemma3-stupidlemma))))
)

(local
(defthm delta-<-0-lemma3-lemma4-stupidlemma
  (implies (and (< a b) (equal b c)) (< a c)))
)

(local
(defthm delta-<-0-lemma3-lemma4
  (implies (basic-params n 3)
	   (< (* 2 n)
	      (expt (gamma) (- 2 (* 2 n)))))
  :hints (("Goal"
	   :do-not '(preprocess simplify)
	   :use ((:instance delta-<-0-lemma3-lemma2)
		 (:instance delta-<-0-lemma3-lemma3)
		 (:instance delta-<-0-lemma3-lemma4-stupidlemma
			    (a (* 2 n))
			    (b (expt (/ (gamma)) (- (* 2 n) 2)))
			    (c (expt (gamma) (- 2 (* 2 n))))))
	   :in-theory (disable delta-<-0-lemma3-lemma2
			       delta-<-0-lemma3-lemma3
			       delta-<-0-lemma3-lemma4-stupidlemma)))
  :rule-classes :linear)
)

(local
(defthm delta-<-0-lemma3
  (implies (basic-params n 3 v0 dv g1)
	   (implies (< (/ (+ (* (expt (gamma) 2)
				(- (fdco (1- (m n g1)) v0 dv g1)
				   (fdco (m n g1) v0 dv g1)))
			     (* (expt (gamma) 1)
				(- (fdco (m n g1) v0 dv g1)
				   (fdco (1+ (m n g1)) v0 dv g1)))
			     (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				   (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c))))) 1))
			  (- 1
			     (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				(1+ (* *beta* (+ (* g1 (1- n)) (equ-c)))))))
		       (* 2 n))
		    (< (/ (+ (* (expt (gamma) 2)
				(- (fdco (1- (m n g1)) v0 dv g1)
				   (fdco (m n g1) v0 dv g1)))
			     (* (expt (gamma) 1)
				(- (fdco (m n g1) v0 dv g1)
				   (fdco (1+ (m n g1)) v0 dv g1)))
			     (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				   (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c))))) 1))
			  (- 1
			     (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				(1+ (* *beta* (+ (* g1 (1- n)) (equ-c)))))))
		       (expt (gamma) (- 2 (* 2 n))))))
  :hints (("Goal"
	   :clause-processor
	   (my-clause-processor clause
				'( (:expand ((:functions ((m integerp)
							  (gamma rationalp)
							  (mu rationalp)
							  (equ-c rationalp)
							  (fdco rationalp)
							  (dv0 rationalp)))
					     (:expansion-level 1)))
				  (:python-file "delta-smaller-than-0-lemma3")
				  (:let ((expt_gamma_2n
					  (expt (gamma) (* 2 n))
					   rationalp)
					 (expt_gamma_2n_minus_1
					  (expt (gamma) (- (* 2 n) 1))
					   rationalp)
					 (expt_gamma_2n_minus_2
					  (expt (gamma) (+ -1 n -1 n))
					   rationalp)
					 (expt_gamma_2
					  (expt (gamma) 2)
					   rationalp)
					 (expt_gamma_1
					  (expt (gamma) 1)
					   rationalp)
					 (expt_gamma_2_minus_2n
					  (expt (gamma) (- 2 (* 2 n)))
					   rationalp))
					 )
				  (:hypothesize ((< (* 2 n) expt_gamma_2_minus_2n)))
				  (:use ((:type ())
				   	 (:hypo ((delta-<-0-lemma3-lemma4)))
				   	 (:main ())))
				  ))
	   :in-theory (disable delta-<-0-lemma3-lemma1
	   		       delta-<-0-lemma3-lemma3-stupidlemma
	   		       delta-<-0-lemma3-lemma2
	   		       delta-<-0-lemma3-lemma3
			       delta-<-0-lemma3-lemma4-stupidlemma)
	   )))
)

(local
(defthm delta-<-0-lemma4
  (implies (basic-params n 3 v0 dv g1)
	   (< (/ (+ (* (expt (gamma) 2)
		       (- (fdco (1- (m n g1)) v0 dv g1)
			  (fdco (m n g1) v0 dv g1)))
		    (* (expt (gamma) 1)
		       (- (fdco (m n g1) v0 dv g1)
			  (fdco (1+ (m n g1)) v0 dv g1)))
		    (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
			  (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c))))) 1))
		 (- 1
		    (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
		       (1+ (* *beta* (+ (* g1 (1- n)) (equ-c)))))))
	      (* 2 n)))
  :hints (("Goal"
	   :clause-processor
	   (my-clause-processor clause
				'( (:expand ((:functions ((m integerp)
							  (gamma rationalp)
							  (mu rationalp)
							  (equ-c rationalp)
							  (fdco rationalp)
							  (dv0 rationalp)))
					     (:expansion-level 1)))
				  (:python-file "delta-smaller-than-0-lemma4")
				  (:let ((expt_gamma_2n
					  (expt (gamma) (* 2 n))
					   rationalp)
					 (expt_gamma_2n_minus_1
					  (expt (gamma) (- (* 2 n) 1))
					   rationalp)
					 (expt_gamma_2n_minus_2
					  (expt (gamma) (+ -1 n -1 n))
					   rationalp)
					 (expt_gamma_2
					  (expt (gamma) 2)
					   rationalp)
					 (expt_gamma_1
					  (expt (gamma) 1)
					   rationalp)
					 (expt_gamma_2_minus_2n
					  (expt (gamma) (- 2 (* 2 n)))
					   rationalp))
					 )
				  (:hypothesize ())))
	   :in-theory (disable delta-<-0-lemma3-lemma1
	   		       delta-<-0-lemma3-lemma3-stupidlemma
	   		       delta-<-0-lemma3-lemma2
	   		       delta-<-0-lemma3-lemma3
			       delta-<-0-lemma3-lemma4-stupidlemma
			       delta-<-0-lemma3-lemma4))))
)


(defthm delta-<-0
  (implies (basic-params n 3 v0 dv g1)
	   (< (delta n v0 dv g1) 0))
  :hints (("Goal"
	   :use ((:instance delta-rewrite-5)
		 (:instance delta-<-0-lemma4)
		 (:instance delta-<-0-lemma3)
		 (:instance delta-<-0-lemma2)
		 (:instance delta-<-0-lemma1))
	   :in-theory (disable delta-<-0-lemma3-lemma1
	   		       delta-<-0-lemma3-lemma3-stupidlemma
	   		       delta-<-0-lemma3-lemma2
	   		       delta-<-0-lemma3-lemma3
			       delta-<-0-lemma3-lemma4-stupidlemma
			       delta-<-0-lemma3-lemma4)
	  )))
) ;; delta < 0 thus is proved

;; prove phi(2n+1) = gamma^2*A+gamma*B+delta
(encapsulate ()

(local
(defthm split-phi-2n+1-lemma1-lemma1
  (implies (basic-params n 3 v0 dv g1 phi0 n)
	   (equal (A (+ n 1) phi0 v0 dv g1)
		  (+ (* (expt (gamma) (+ (* 2 n) 1)) phi0)
		     (* (expt (gamma) (* 2 n))
			(- (fdco (1- (m n g1)) v0 dv g1) 1))
		     (* (expt (gamma) (- (* 2 n) 1))
			(- (fdco (m n g1) v0 dv g1) 1))))))
)

(local
(defthm split-phi-2n+1-lemma1-lemma2
  (implies (basic-params n 3 v0 dv g1 phi0 n)
	   (equal (+ (* (expt (gamma) (+ (* 2 n) 1)) phi0)
		     (* (expt (gamma) (* 2 n))
			(- (fdco (1- (m n g1)) v0 dv g1) 1))
		     (* (expt (gamma) (- (* 2 n) 1))
			(- (fdco (m n g1) v0 dv g1) 1)))
		  (+ (* (+ (* (expt (gamma) (- (* 2 n) 1)) phi0)
			   (* (expt (gamma) (- (* 2 n) 2))
			      (- (fdco (m n g1) v0 dv g1) 1))
			   (* (expt (gamma) (- (* 2 n) 3))
			      (- (fdco (1+ (m n g1)) v0 dv g1) 1)))
			(expt (gamma) 2))
		     (- (* (expt (gamma) (* 2 n))
			   (- (fdco (1- (m n g1)) v0 dv g1) 1))
			(* (expt (gamma) (* 2 n))
			   (- (fdco (m n g1) v0 dv g1) 1)))
		     (- (* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (m n g1) v0 dv g1) 1))
			(* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (1+ (m n g1)) v0 dv g1) 1))))))
  )
)

(local
(defthm split-phi-2n+1-lemma1-A
  (implies (basic-params n 3 v0 dv g1 phi0 n)
	   (equal (A (+ n 1) phi0 v0 dv g1)
		  (+ (* (A n phi0 v0 dv g1) (gamma) (gamma))
		     (- (* (expt (gamma) (* 2 n))
			   (- (fdco (1- (m n g1)) v0 dv g1) 1))
			(* (expt (gamma) (* 2 n))
			   (- (fdco (m n g1) v0 dv g1) 1)))
		     (- (* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (m n g1) v0 dv g1) 1))
			(* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (1+ (m n g1)) v0 dv g1) 1)))))))
)

(local
(defthm split-phi-2n+1-lemma2-lemma1
  (implies (basic-params n 3 v0 dv g1)
	   (equal (B (+ n 1) v0 dv g1)
		  (* (expt (gamma) (- n 1))
		     (B-sum 1 (- n 1) v0 dv g1)))))
)

(local
(defthm split-phi-2n+1-lemma2-lemma2
  (implies (basic-params n 3 v0 dv g1)
	   (equal (B (+ n 1) v0 dv g1)
		  (* (expt (gamma) (- n 1))
		     (+ (B-term (- n 1) v0 dv g1)
			(B-term (- (- n 1)) v0 dv g1)
			(B-sum 1 (- n 2) v0 dv g1))))))
)

(local
(defthm split-phi-2n+1-lemma2-lemma3
  (implies (basic-params n 3 v0 dv g1)
	   (equal (B (+ n 1) v0 dv g1)
		  (+ (* (expt (gamma) (- n 1))
			(B-sum 1 (- n 2) v0 dv g1))
		     (* (expt (gamma) (- n 1))
			(B-term (- n 1) v0 dv g1))
		     (* (expt (gamma) (- n 1))
			(B-term (- (- n 1)) v0 dv g1))))))
)

(local
(defthm split-phi-2n+1-lemma2-lemma4
  (implies (basic-params n 3 v0 dv g1)
	   (equal (B (+ n 1) v0 dv g1)
		  (+ (* (gamma) (expt (gamma) (- n 2))
			(B-sum 1 (- n 2) v0 dv g1))
		     (* (expt (gamma) (- n 1))
			(+ (B-term (- n 1) v0 dv g1)
			   (B-term (- (- n 1)) v0 dv g1)))))))
)

(local
(defthm split-phi-2n+1-lemma2-lemma5
  (implies (basic-params n 3 v0 dv g1)
	   (equal (B (+ n 1) v0 dv g1)
		  (+ (* (gamma) (B n v0 dv g1))
		     (* (expt (gamma) (- n 1))
			(+ (B-term (- n 1) v0 dv g1)
			   (B-term (- (- n 1)) v0 dv g1)))))))
)

(local
(defthm split-phi-2n+1-lemma2-B
  (implies (basic-params n 3 v0 dv g1)
	   (equal (B (+ n 1) v0 dv g1)
		  (+ (* (gamma) (B n v0 dv g1))
		     (* (expt (gamma) (- n 1))
			(+ (* (expt (gamma) (- (- n 1)))
			      (B-term-rest (- n 1) v0 dv g1))
			   (* (expt (gamma) (- n 1))
			      (B-term-rest (- (- n 1)) v0 dv g1))))))))
)

(local
(defthm split-phi-2n+1-lemma3-delta-stupidlemma
  (implies (basic-params n 3 v0 dv g1)
	   (equal (+ (- (* (expt (gamma) (* 2 n))
			   (- (fdco (1- (m n g1)) v0 dv g1) 1))
			(* (expt (gamma) (* 2 n))
			   (- (fdco (m n g1) v0 dv g1) 1)))
		     (- (* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (m n g1) v0 dv g1) 1))
			(* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (1+ (m n g1)) v0 dv g1) 1)))
		     (* (expt (gamma) (- n 1))
			(+ (* (expt (gamma) (- (- n 1)))
			      (B-term-rest (- n 1) v0 dv g1))
			   (* (expt (gamma) (- n 1))
			      (B-term-rest (- (- n 1)) v0 dv g1)))))
		  (+ (- (* (expt (gamma) (* 2 n))
			   (- (fdco (1- (m n g1)) v0 dv g1) 1))
			(* (expt (gamma) (* 2 n))
			   (- (fdco (m n g1) v0 dv g1) 1)))
		     (- (* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (m n g1) v0 dv g1) 1))
			(* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (1+ (m n g1)) v0 dv g1) 1)))
		     (* (expt (gamma) (1- n))
			(+ (* (expt (gamma) (1+ (- n)))
			      (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				    (1+ (* *beta* (+ (* g1 (1- n)) (equ-c))))) 1))
			   (* (expt (gamma) (1- n))
			      (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				    (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c))))) 1))))))))
)

(local
(defthm split-phi-2n+1-lemma3-delta
  (implies (basic-params n 3 v0 dv g1)
	   (equal (+ (- (* (expt (gamma) (* 2 n))
			   (- (fdco (1- (m n g1)) v0 dv g1) 1))
			(* (expt (gamma) (* 2 n))
			   (- (fdco (m n g1) v0 dv g1) 1)))
		     (- (* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (m n g1) v0 dv g1) 1))
			(* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (1+ (m n g1)) v0 dv g1) 1)))
		     (* (expt (gamma) (- n 1))
			(+ (* (expt (gamma) (- (- n 1)))
			      (B-term-rest (- n 1) v0 dv g1))
			   (* (expt (gamma) (- n 1))
			      (B-term-rest (- (- n 1)) v0 dv g1)))))
		  (delta n v0 dv g1)))
  :hints (("Goal"
	   :use ((:instance split-phi-2n+1-lemma3-delta-stupidlemma)
		 (:functional-instance (:instance delta)))
	   :in-theory '(minimal-theory))))
)

(local
(defthm split-phi-2n+1-lemma4
  (implies (basic-params n 3 v0 dv g1 phi0 n)
	   (equal (phi-2n-1 (1+ n) phi0 v0 dv g1)
		  (+ (A (+ n 1) phi0 v0 dv g1)
		     (B (+ n 1) v0 dv g1)))))
)

(local
(defthm split-phi-2n+1-lemma5
  (implies (basic-params n 3 v0 dv g1 phi0 n)
	   (equal (phi-2n-1 (1+ n) phi0 v0 dv g1)
		  (+ (+ (* (A n phi0 v0 dv g1) (gamma) (gamma))
			(- (* (expt (gamma) (* 2 n))
			      (- (fdco (1- (m n g1)) v0 dv g1) 1))
			   (* (expt (gamma) (* 2 n))
			      (- (fdco (m n g1) v0 dv g1) 1)))
			(- (* (expt (gamma) (- (* 2 n) 1))
			      (- (fdco (m n g1) v0 dv g1) 1))
			   (* (expt (gamma) (- (* 2 n) 1))
			      (- (fdco (1+ (m n g1)) v0 dv g1) 1))))
		     (+ (* (gamma) (B n v0 dv g1))
			(* (expt (gamma) (- n 1))
			   (+ (* (expt (gamma) (- (- n 1)))
				 (B-term-rest (- n 1) v0 dv g1))
			      (* (expt (gamma) (- n 1))
				 (B-term-rest (- (- n 1)) v0 dv g1))))))))
  :hints (("Goal"
	   :use ((:instance split-phi-2n+1-lemma1-A)
		 (:instance split-phi-2n+1-lemma2-B)))))
)

(local 
(defthm split-phi-2n+1-lemma6
  (implies (basic-params n 3 v0 dv g1 phi0 n)
	   (equal (phi-2n-1 (1+ n) phi0 v0 dv g1)
		  (+ (* (A n phi0 v0 dv g1) (gamma) (gamma))
		     (* (gamma) (B n v0 dv g1))
		     (+ (- (* (expt (gamma) (* 2 n))
			      (- (fdco (1- (m n g1)) v0 dv g1) 1))
			   (* (expt (gamma) (* 2 n))
			      (- (fdco (m n g1) v0 dv g1) 1)))
			(- (* (expt (gamma) (- (* 2 n) 1))
			      (- (fdco (m n g1) v0 dv g1) 1))
			   (* (expt (gamma) (- (* 2 n) 1))
			      (- (fdco (1+ (m n g1)) v0 dv g1) 1)))
			(* (expt (gamma) (- n 1))
			   (+ (* (expt (gamma) (- (- n 1)))
				 (B-term-rest (- n 1) v0 dv g1))
			      (* (expt (gamma) (- n 1))
				 (B-term-rest (- (- n 1)) v0 dv g1)))))))))
)

(defthm split-phi-2n+1
  (implies (basic-params n 3 v0 dv g1 phi0 n)
	   (equal (phi-2n-1 (1+ n) phi0 v0 dv g1)
 		  (+ (* (gamma) (gamma) (A n phi0 v0 dv g1))
		     (* (gamma) (B n v0 dv g1)) (delta n v0 dv g1))))
  :hints (("Goal"
	   :use ((:instance split-phi-2n+1-lemma6)
		 (:instance split-phi-2n+1-lemma3-delta)))))

)

;; prove gamma^2*A + gamma*B < 0
(encapsulate ()

(local
(defthm except-for-delta-<-0-lemma1
  (implies (and (and (rationalp c)
		     (rationalp a)
		     (rationalp b))
		(and (> c 0)
		     (< c 1)
		     (< (+ A B) 0)
		     (< B 0)))
	   (< (+ (* c c A) (* c B)) 0))
  :hints (("Goal"
	   :clause-processor
	   (my-clause-processor clause
				'( (:expand ((:function ())
					     (:expansion-level 1)))
				  (:python-file "except-for-delta-smaller-than-0-lemma1")
				  (:let ())
				  (:hypothesize ())))))
  :rule-classes :linear)
)

(defthm except-for-delta-<-0
  (implies (basic-params n 3 v0 dv g1 phi0 n (< (phi-2n-1 n phi0 v0 dv g1) 0))
	   (< (+ (* (gamma) (gamma) (A n phi0 v0 dv g1))
		 (* (gamma) (B n v0 dv g1)))
	      0))
  :hints (("Goal"
	   :do-not-induct t
	   :use ((:instance except-for-delta-<-0-lemma1
			    (c (gamma))
			    (A (A n phi0 v0 dv g1))
			    (B (B n v0 dv g1)))
		 (:instance B-neg)))))
)

;; for induction step 
(encapsulate ()
(defthm phi-2n+1-<-0-lemma1
  (implies (basic-params n 3 v0 dv g1 phi0 n (< (phi-2n-1 n phi0 v0 dv g1) 0))
	   (< (phi-2n-1 (1+ n) phi0 v0 dv g1) 0))
  :hints (("Goal"
 	   :use ((:instance split-phi-2n+1)
		 (:instance delta-<-0)
		 (:instance except-for-delta-<-0)))))

(defthm phi-2n+1-<-0
  (implies (basic-params n 4 v0 dv g1 phi0 (- n 1) (< (phi-2n-1 (- n 1) phi0 v0 dv g1) 0))
	   (< (phi-2n-1 n phi0 v0 dv g1) 0))
  :hints (("Goal"
	   :use ((:instance phi-2n+1-<-0-lemma1
			    (n (- n 1)))))))

(defthm phi-2n+1-<-0-corollary-1
  (implies (basic-params n 4 v0 dv g1 phi0 (- n 1) 
			 (< (+ (A (- n 1) phi0 v0 dv g1)
			       (* (expt (gamma) (- (- n 1) 2))
				  (B-sum 1 (- (- n 1) 2) v0 dv g1)))
			    0))
	   (< (+ (A n phi0 v0 dv g1)
		 (* (expt (gamma) (- n 2))
		    (B-sum 1 (- n 2) v0 dv g1)))
	      0))
  :hints (("Goal"
	   :use ((:instance phi-2n+1-<-0)))))

(defthm phi-2n+1-<-0-corollary-2
  (implies (basic-params n-minus-2 2 v0 dv g1 phi0 (- (+ n-minus-2 2) 1)
			 (< (+ (A (+ n-minus-2 1) phi0 v0 dv g1)
			       (* (expt (gamma) (- n-minus-2 1))
				  (B-sum 1 (- n-minus-2 1) v0 dv g1)))
			    0))
	   (< (+ (A (+ n-minus-2 2) phi0 v0 dv g1)
		 (* (expt (gamma) n-minus-2)
		    (B-sum 1 n-minus-2 v0 dv g1)))
	      0))
  :hints (("Goal"
	   :use ((:instance phi-2n+1-<-0-corollary-1
			    (n (+ n-minus-2 2)))))))
)

(encapsulate ()

(defthm phi-2n-1-<-0-base
  (implies (basic-params-equal n 3 v0 dv g1 phi0 n)
	   (< (phi-2n-1 n phi0 v0 dv g1) 0))
  :hints (("Goal''"
	   :do-not '(simplify))))
)

;; induction step
(encapsulate ()

;; CANNOT PROVE
(local
(defthm phi-2n-1-<-0-inductive-lemma1-lemma1-stupidlemma-lemma
  (implies (and (and (rationalp v0)
		     (rationalp phi0))
		(and (<= 1 (* 10/9 v0))
		     (<= v0 11/10)
		     (<= 0 phi0)
		     (< phi0
			(+ -1 (* (+ 1 v0) (/ (+ 1599/1600 v0)))))))
         (< (+ (* 1/3125 phi0)
               (* (+ 1 v0) (/ (+ 3201/3200 v0)))
               (* 1/125 (+ 1 v0) (/ (+ 1599/1600 v0)))
               (* 1/25 (+ 1 v0) (/ (+ 3199/3200 v0)))
               (* 1/625 (+ 1 v0) (/ (+ 3197/3200 v0))))
            656/625))
  :hints (("Goal"
	   :clause-processor
	   (my-clause-processor clause
				'( (:expand ((:function ())
					     (:expansion-level 1)))
				  (:python-file "phi-2n-1-smaller-than-0-lemma1-lemma1-stupidlemma-lemma")
				  (:let ())
				  (:hypothesize ()))))))
)

(local
(defthm phi-2n-1-<-0-inductive-lemma1-lemma1-stupidlemma
  (implies (basic-params-equal n-minus-2 1 v0 dv g1 phi0 (+ n-minus-2 2))
	   (< (+ (A (+ n-minus-2 2) phi0 v0 dv g1)
		 (* (expt (gamma) n-minus-2)
		    (B-sum 1 n-minus-2 v0 dv g1))) 0))
  :hints (("Goal''"
	   :use ((:instance phi-2n-1-<-0-inductive-lemma1-lemma1-stupidlemma-lemma)))))
)

(local
(defthm phi-2n-1-<-0-inductive-lemma1-lemma1-lemma1
  (implies (basic-params n_minus_2 2 v0 dv g1 phi0 (+ n_minus_2 2))
	   (and (< phi0 (+ -1 (fdco (+ 1 (m (+ -1 n_minus_2 2) g1)) v0 dv g1)))
		(> (+ -1 (fdco (+ 1 (m (+ n_minus_2 2) g1)) v0 dv g1)) 0)
		(> (+ -1 (fdco (+ 1 (m (+ -1 n_minus_2 2) g1)) v0 dv g1)) 0)))
  :hints (("Goal"
	   :clause-processor
	   (my-clause-processor clause
				'( (:expand ((:functions ((fdco rationalp)
							  (m integerp)
							  (mu rationalp)
							  (equ-c rationalp)
							  (dv0 rationalp)))
					     (:expansion-level 1)))
				  (:python-file "phi-2n-1-smaller-than-0-inductive-lemma1-lemma1-lemma1")
				  (:let ())
				  (:hypothesize ()))))))
)

(local
(defthm phi-2n-1-<-0-inductive-lemma1-lemma1-lemma2
  (implies (integerp n-minus-2)
	   (integerp (+ -1 n-minus-2))))
)

(local
(defthm phi-2n-1-<-0-inductive-lemma1-lemma1
  (implies (basic-params n-minus-2 1 v0 dv g1 phi0 (+ n-minus-2 2))
	   (< (+ (A (+ n-minus-2 2) phi0 v0 dv g1)
		 (* (expt (gamma) n-minus-2)
		    (B-sum 1 n-minus-2 v0 dv g1))) 0))
  )
)

(local
(defthm phi-2n-1-<-0-inductive-lemma1
  (implies (basic-params n 3 v0 dv g1 phi0 n)
	   (< (+ (A n phi0 v0 dv g1)
		 (* (expt (gamma) (- n 2))
		    (B-sum 1 (- n 2) v0 dv g1))) 0))
  :hints (("Goal"
	   :use ((:instance phi-2n-1-<-0-inductive-lemma1-lemma1
			    (n-minus-2 (- n 2)))))))
)

(local
(defthm phi-2n-1-<-0-inductive-lemma2
  (implies (basic-params n 3 v0 dv g1 phi0 n)
	   (< (+ (A n phi0 v0 dv g1) (B n v0 dv g1)) 0))
  :hints (("Goal"
	   :use ((:instance phi-2n-1-<-0-inductive-lemma1)))))
)

(defthm phi-2n-1-<-0-inductive
  (implies (basic-params n 3 v0 dv g1 phi0 n)
	   (< (phi-2n-1 n phi0 v0 dv g1) 0))
  :hints (("Goal"
	   :use ((:instance phi-2n-1-<-0-inductive-lemma2)))))
)

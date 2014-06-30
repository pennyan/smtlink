(in-package "ACL2")
(include-book "global")
(include-book "arithmetic/top-with-meta" :dir :system)

;; for the clause processor to work
(include-book "../smtlink/SMT-connect")
(logic)
:set-state-ok t
:set-ignore-ok t

(defun fdco (n v0 g1)
  (/ (* (mu) (+ 1 (* *alpha* v0))) (+ 1 (* *beta* n g1))))

(defun B-term-expt (h)
  (expt (gamma) (- h)))

(defun B-term-rest (h v0 g1)
  (- (* (mu) (/ (+ 1 (* *alpha* v0)) (+ 1 (* *beta* (+ (* h g1) (equ-c v0)))))) 1))

(defun B-term (h v0 g1)
  (* (expt (gamma) (- h)) (- (* (mu) (/ (+ 1 (* *alpha* v0)) (+ 1 (* *beta* (+ (* h g1) (equ-c v0)))))) 1)))

(defun B-sum (h_lo h_hi v0 g1)
  (declare (xargs :measure (if (or (not (integerp h_lo))
				   (not (integerp h_hi))
				   (< h_hi h_lo))
			       0
			       (1+ (- h_hi h_lo)))))
  (if (or (not (integerp h_hi)) (not (integerp h_lo)) (> h_lo h_hi))  0
      (+ (B-term h_hi v0 g1) (B-term (- h_hi) v0 g1) (B-sum h_lo (- h_hi 1) v0 g1))))

(defun B-expt (n)
  (expt (gamma) (- n 2)))

(defun B (n v0 g1)
  (* (expt (gamma) (- n 2))
     (B-sum 1 (- n 2) v0 g1)))

(encapsulate ()

(local
 (defthm B-term-neg-lemma1
     (equal (B-term h v0 g1) (* (B-term-expt h) (B-term-rest h v0 g1)))))

(local
 (defthm B-term-neg-lemma2
     (equal (B-term (- h) v0 g1) (* (B-term-expt (- h)) (B-term-rest (- h) v0 g1)))))

(local
(defthm B-term-neg-lemma3
  (implies (and (and (integerp h) (rationalp v0) (rationalp g1))
		(and (>= h 1) (>= v0 9/10) (<= v0 11/10) (equal g1 1/3200)))
	   (< (+ (* (B-term-expt h) (B-term-rest h v0 g1))
		 (* (B-term-expt (- h)) (B-term-rest (- h) v0 g1)))
	      0))
  :hints
  (("Goal"
    :clause-processor
    (my-clause-processor clause
			 '( (:expand (B-term-rest gamma mu equ-c))
			    (:python-file "B-term-neg-lemma3") ;;mktemp
			    (:let ((expt_gamma_h (B-term-expt h) rationalp)
				   (expt_gamma_minus_h (B-term-expt (- h)) rationalp)))
			    (:hypothesize ((> expt_gamma_h 1)
					   (equal expt_gamma_minus_h (/ expt_gamma_h))))))
    )))
)

(defthm B-term-neg
  (implies (and (and (integerp h) (rationalp v0) (rationalp g1))
		(and (>= h 1) (>= v0 9/10) (<= v0 11/10) (equal g1 1/3200)))
	   (< (+ (B-term h v0 g1) (B-term (- h) v0 g1)) 0))
  :hints (("Goal"
	   :use ((:instance B-term-neg-lemma1)
		 (:instance B-term-neg-lemma2)
		 (:instance B-term-neg-lemma3))))
  :rule-classes :linear)
)

(defthm B-sum-neg
  (implies (and (and (integerp n-minus-2) (rationalp v0) (rationalp g1))
		(and (>= n-minus-2 1) (>= v0 9/10) (<= v0 11/10) (equal g1 1/3200)))
	   (< (B-sum 1 n-minus-2 v0 g1) 0))
  :hints (("Goal"
	   :in-theory (disable B-term)))
  :rule-classes :linear)

(encapsulate ()
	     
(local ;; B = B-expt*B-sum
 (defthm B-neg-lemma1
   (implies (and (and (integerp n) (rationalp v0) (rationalp g1))
		 (and (> n 2) (>= v0 9/10) (<= v0 11/10) (equal g1 1/3200)))
	    (equal (B n v0 g1)
		   (* (B-expt n)
		      (B-sum 1 (- n 2) v0 g1))))))

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
   (implies (and (and (integerp n-minus-2) (rationalp v0) (rationalp g1)))
		 ;;(and (>= n-minus-2 1) (>= v0 9/10) (<= v0 11/10) (equal g1 1/3200)))
	    (rationalp (B-sum 1 n-minus-2 v0 g1)))
   :rule-classes :type-prescription))

(local
 (defthm B-neg-type-lemma4
   (implies (and (integerp n) (> n 2))
	    (rationalp (B-expt n)))
   :rule-classes :type-prescription))

(defthm B-neg
  (implies (and (and (integerp n) (rationalp v0) (rationalp g1))
		(and (> n 2) (>= v0 9/10) (<= v0 11/10) (equal g1 1/3200)))
	   (< (B n v0 g1) 0))
  :hints (("Goal"
	   :do-not-induct t
	   :in-theory (disable B-expt B-sum B-sum-neg B-expt->-0)
	   :use ((:instance B-sum-neg (n-minus-2 (- n 2)))
		 (:instance B-expt->-0)
		 (:instance B-neg-type-lemma3 (n-minus-2 (- n 2)))
		 (:instance B-neg-type-lemma4)
		 (:instance B-neg-lemma2 (a (B-expt n))
			                 (b (B-sum 1 (+ -2 n) v0 g1)))))))
)

(defun A (n phi0 v0 g1)
  (+ (* (expt (gamma) (- (* 2 n) 1)) phi0)
     (* (expt (gamma) (- (* 2 n) 2))
	(- (fdco (m n v0 g1) v0 g1) 1))
     (* (expt (gamma) (- (* 2 n) 3))
	(- (fdco (1+ (m n v0 g1)) v0 g1) 1))))

(defun phi-2n-1 (n phi0 v0 g1)
  (+ (A n phi0 v0 g1) (B n v0 g1)))

(defun delta (n v0 g1)
  (+ (- (* (expt (gamma) (* 2 n))
	   (- (fdco (1- (m n v0 g1)) v0 g1) 1))
	(* (expt (gamma) (* 2 n)) 
	   (- (fdco (m n v0 g1) v0 g1) 1)))
     (- (* (expt (gamma) (- (* 2 n) 1))
	   (- (fdco (m n v0 g1) v0 g1) 1))
	(* (expt (gamma) (- (* 2 n) 1))
	   (- (fdco (1+ (m n v0 g1)) v0 g1) 1)))
     (* (expt (gamma) (1- n))
	(+ (* (expt (gamma) (1+ (- n)))
	      (- (/ (* (mu) (1+ (* *alpha* v0)))
		    (1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0)))))
		 1))
	   (* (expt (gamma) (1- n))
	      (- (/ (* (mu) (1+ (* *alpha* v0)))
		    (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0)))))
		 1))))))

(defun delta-1 (n v0 g1)
  (+ (* (expt (gamma) (* 2 n))
	(- (fdco (1- (m n v0 g1)) v0 g1)
	   (fdco (m n v0 g1) v0 g1)))
     (* (expt (gamma) (- (* 2 n) 1))
	(- (fdco (m n v0 g1) v0 g1)
	   (fdco (1+ (m n v0 g1)) v0 g1)))
     (* (* (expt (gamma) (1- n)) (expt (gamma) (1+ (- n))))
	(- (/ (* (mu) (1+ (* *alpha* v0)))
	      (1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0))))) 1))
     (* (* (expt (gamma) (1- n)) (expt (gamma) (1- n)))
	(- (/ (* (mu) (1+ (* *alpha* v0)))
	      (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1))))

(defun delta-2 (n v0 g1)
  (+ (* (expt (gamma) (* 2 n))
	(- (fdco (1- (m n v0 g1)) v0 g1)
	   (fdco (m n v0 g1) v0 g1)))
     (* (expt (gamma) (- (* 2 n) 1))
	(- (fdco (m n v0 g1) v0 g1)
	   (fdco (1+ (m n v0 g1)) v0 g1)))
     (- (/ (* (mu) (1+ (* *alpha* v0)))
	   (1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0))))) 1)
     (* (expt (gamma) (+ -1 n -1 n))
	(- (/ (* (mu) (1+ (* *alpha* v0)))
	      (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1))))

(defun delta-3 (n v0 g1)
  (* (expt (gamma) (+ -1 n -1 n))
     (+ (* (expt (gamma) 2)
	   (- (fdco (1- (m n v0 g1)) v0 g1)
	      (fdco (m n v0 g1) v0 g1)))
	(* (expt (gamma) 1)
	   (- (fdco (m n v0 g1) v0 g1)
	      (fdco (1+ (m n v0 g1)) v0 g1)))
	(* (expt (gamma) (- 2 (* 2 n)))
	   (- (/ (* (mu) (1+ (* *alpha* v0)))
		 (1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0))))) 1))
	(- (/ (* (mu) (1+ (* *alpha* v0)))
	      (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1))))

(defun delta-3-inside (n v0 g1)
  (+ (* (expt (gamma) 2)
	   (- (fdco (1- (m n v0 g1)) v0 g1)
	      (fdco (m n v0 g1) v0 g1)))
	(* (expt (gamma) 1)
	   (- (fdco (m n v0 g1) v0 g1)
	      (fdco (1+ (m n v0 g1)) v0 g1)))
	(* (expt (gamma) (- 2 (* 2 n)))
	   (- (/ (* (mu) (1+ (* *alpha* v0)))
		 (1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0))))) 1))
	(- (/ (* (mu) (1+ (* *alpha* v0)))
	      (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1)))

(defun delta-3-inside-transform (n v0 g1)
  (/ 
   (+ (* (expt (gamma) 2)
	 (- (fdco (1- (m n v0 g1)) v0 g1)
	    (fdco (m n v0 g1) v0 g1)))
      (* (expt (gamma) 1)
	 (- (fdco (m n v0 g1) v0 g1)
	    (fdco (1+ (m n v0 g1)) v0 g1)))
      (- (/ (* (mu) (1+ (* *alpha* v0)))
	    (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1))
   (- 1
      (/ (* (mu) (1+ (* *alpha* v0)))
	 (1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0))))))))

;; rewrite delta term
(encapsulate ()

(local
;; considering using smtlink for the proof, probably simpler
(defthm delta-rewrite-1-lemma1
  (implies (and (and (integerp n) (rationalp v0) (rationalp g1))
		(and (>= n 3) (>= v0 9/10) (<= v0 11/10) (equal g1 1/3200)))
	   (equal (+ (- (* (expt (gamma) (* 2 n))
			   (- (fdco (1- (m n v0 g1)) v0 g1) 1))
			(* (expt (gamma) (* 2 n))
			   (- (fdco (m n v0 g1) v0 g1) 1)))
		     (- (* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (m n v0 g1) v0 g1) 1))
			(* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (1+ (m n v0 g1)) v0 g1) 1)))
		     (* (expt (gamma) (1- n))
			(+ (* (expt (gamma) (1+ (- n)))
			      (- (/ (* (mu) (1+ (* *alpha* v0)))
				    (1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0)))))
				 1))
			   (* (expt (gamma) (1- n))
			      (- (/ (* (mu) (1+ (* *alpha* v0)))
				    (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0)))))
				 1)))))
		    (+ (* (expt (gamma) (* 2 n))
			  (- (fdco (1- (m n v0 g1)) v0 g1)
			     (fdco (m n v0 g1) v0 g1)))
		       (* (expt (gamma) (- (* 2 n) 1))
			  (- (fdco (m n v0 g1) v0 g1)
			     (fdco (1+ (m n v0 g1)) v0 g1)))
		       (* (* (expt (gamma) (1- n)) (expt (gamma) (1+ (- n))))
			  (- (/ (* (mu) (1+ (* *alpha* v0)))
				(1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0))))) 1))
		       (* (* (expt (gamma) (1- n)) (expt (gamma) (1- n)))
			  (- (/ (* (mu) (1+ (* *alpha* v0)))
				(1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1)))))
  :hints
  (("Goal"
    :clause-processor
    (my-clause-processor clause
			 '( (:expand (m gamma mu equ-c fdco))
			    (:python-file "delta-rewrite-1-lemma1") ;;mktemp
			    (:let ((expt_gamma_2n
				    (expt (gamma) (* 2 n))
				     rationalp)
				   (expt_gamma_2n_minus_1
				    (expt (gamma) (- (* 2 n) 1))
				     rationalp)
				   (expt_gamma_n_minus_1
				    (expt (gamma) (1- n))
				     rationalp)
				   (expt_gamma_1_minus_n
				    (expt (gamma) (1+ (- n)))
				     rationalp)
				   ))
			    (:hypothesize ())))
    )))
)

(local
(defthm delta-rewrite-1
  (implies (and (and (integerp n) (rationalp v0) (rationalp g1))
		(and (>= n 3) (>= v0 9/10) (<= v0 11/10) (equal g1 1/3200)))
	   (equal (delta n v0 g1)
		  (delta-1 n v0 g1))))
)

(local
(defthm delta-rewrite-2-lemma1
  (implies (and (integerp n)
		(>= n 3))
	   (equal (* (expt (gamma) (1- n))
		     (expt (gamma) (1+ (- n))))
		  1))
  :hints (("Goal"
	   :use ((:instance expt-minus
			    (r (gamma))
			    (i (- (1+ (- n)))))))))
)

(local
(defthm delta-rewrite-2-lemma2
  (implies (and (integerp n)
		(>= n 3))
 	   (equal (* (expt (gamma) (1- n))
 		     (expt (gamma) (1- n)))
		  (expt (gamma) (+ -1 n -1 n))))
  :hints (("Goal"
	   :do-not-induct t
	   :use ((:instance exponents-add-for-nonneg-exponents
			    (i (1- n))
			    (j (1- n))
			    (r (gamma))))
	   :in-theory (disable exponents-add-for-nonneg-exponents))))
)

(local
(defthm delta-rewrite-2-lemma3
  (implies (and (integerp n)
		(>= n 3))
	   (equal (+ A
		     B
		     (* (* (expt (gamma) (1- n))
			   (expt (gamma) (1+ (- n))))
			C)
		     (* (* (expt (gamma) (1- n))
			   (expt (gamma) (1- n)))
			D))
		  (+ A B C
		     (* (expt (gamma) (+ -1 n -1 n)) D))))
  :hints (("Goal"
	   :use ((:instance delta-rewrite-2-lemma1)
		 (:instance delta-rewrite-2-lemma2)))))
)

(local
(defthm delta-rewrite-2
  (implies (and (and (integerp n) (rationalp v0) (rationalp g1))
		(and (>= n 3) (>= v0 9/10) (<= v0 11/10) (equal g1 1/3200)))
	   (equal (delta-1 n v0 g1)
		  (delta-2 n v0 g1)))
  :hints (("Goal"
	   :use ((:instance delta-rewrite-2-lemma3
			    (A (* (expt (gamma) (* 2 n))
				  (- (fdco (1- (m n v0 g1)) v0 g1)
				     (fdco (m n v0 g1) v0 g1))))
			    (B (* (expt (gamma) (- (* 2 n) 1))
				  (- (fdco (m n v0 g1) v0 g1)
				     (fdco (1+ (m n v0 g1)) v0 g1))))
			    (C (- (/ (* (mu) (1+ (* *alpha* v0)))
				     (1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0))))) 1))
			    (D (- (/ (* (mu) (1+ (* *alpha* v0)))
				     (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1)))))))
)

(local
(defthm delta-rewrite-3-lemma1-lemma1
  (implies (and (integerp n)
		(>= n 3))
	   (equal (expt (gamma) (+ (+ -1 n -1 n) 2))
		  (* (expt (gamma) (+ -1 n -1 n))
		     (expt (gamma) 2))))
  :hints (("Goal"
	   :use ((:instance exponents-add-for-nonneg-exponents
			    (i (+ -1 n -1 n))
			    (j 2)
			    (r (gamma))))
	   :in-theory (disable exponents-add-for-nonneg-exponents
			       delta-rewrite-2-lemma2))))
)

(local
(defthm delta-rewrite-3-lemma1-stupidlemma
  (implies (and (integerp n)
		(>= n 3))
	   (equal (* 2 n) (+ (+ -1 n -1 n) 2))))
)

(local
(defthm delta-rewrite-3-lemma1
  (implies (and (integerp n)
		(>= n 3))
	   (equal (expt (gamma) (* 2 n))
		  (* (expt (gamma) (+ -1 n -1 n))
		     (expt (gamma) 2)))))
)

(local
(defthm delta-rewrite-3-lemma2-lemma1
  (implies (and (integerp n)
		(>= n 3))
	   (equal (expt (gamma) (+ (+ -1 n -1 n) 1))
		  (* (expt (gamma) (+ -1 n -1 n))
		     (expt (gamma) 1))))
  :hints (("Goal"
	   :use ((:instance exponents-add-for-nonneg-exponents
			    (i (+ -1 n -1 n))
			    (j 1)
			    (r (gamma))))
	   :in-theory (disable exponents-add-for-nonneg-exponents
			       delta-rewrite-2-lemma2))))
)

(local
(defthm delta-rewrite-3-lemma2-stupidlemma
  (implies (and (integerp n)
		(>= n 3))
	   (equal (- (* 2 n) 1) (+ (+ -1 n -1 n) 1))))
)

(local
(defthm delta-rewrite-3-lemma2
  (implies (and (integerp n)
		(>= n 3))
	   (equal (expt (gamma) (- (* 2 n) 1))
		  (* (expt (gamma) (+ -1 n -1 n))
		     (expt (gamma) 1))))
  :hints (("Goal"
	   :use ((:instance delta-rewrite-3-lemma2-lemma1)
		 (:instance delta-rewrite-3-lemma2-stupidlemma))
	   :in-theory (disable delta-rewrite-2-lemma1))))
)

(local
(defthm delta-rewrite-3-lemma3
  (implies (and (integerp n)
		(>= n 3))
	   (equal (* (expt (gamma) (- 2 (* 2 n)))
		     (expt (gamma) (+ -1 n -1 n)))
		  1))
  :hints (("Goal"
	   :use ((:instance expt-minus
			    (r (gamma))
			    (i (- (- 2 (* 2 n)))))))))
)

(local
(defthm delta-rewrite-3
  (implies (and (and (integerp n) (rationalp v0) (rationalp g1))
		(and (>= n 3) (>= v0 9/10) (<= v0 11/10) (equal g1 1/3200)))
	   (equal (+ (* (expt (gamma) (* 2 n))
			(- (fdco (1- (m n v0 g1)) v0 g1)
			   (fdco (m n v0 g1) v0 g1)))
		     (* (expt (gamma) (- (* 2 n) 1))
			(- (fdco (m n v0 g1) v0 g1)
			   (fdco (1+ (m n v0 g1)) v0 g1)))
		     (- (/ (* (mu) (1+ (* *alpha* v0)))
			   (1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0))))) 1)
		     (* (expt (gamma) (+ -1 n -1 n))
			(- (/ (* (mu) (1+ (* *alpha* v0)))
			      (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1)))
		  (* (expt (gamma) (+ -1 n -1 n))
		     (+ (* (expt (gamma) 2)
			   (- (fdco (1- (m n v0 g1)) v0 g1)
			      (fdco (m n v0 g1) v0 g1)))
			(* (expt (gamma) 1)
			   (- (fdco (m n v0 g1) v0 g1)
			      (fdco (1+ (m n v0 g1)) v0 g1)))
			(* (expt (gamma) (- 2 (* 2 n)))
			   (- (/ (* (mu) (1+ (* *alpha* v0)))
				 (1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0))))) 1))
			(- (/ (* (mu) (1+ (* *alpha* v0)))
			      (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1)))))
  :hints
  (("Goal"
    :do-not '(simplify)
    :in-theory (disable delta-rewrite-2-lemma1 expt)
    :do-not-induct t
    :clause-processor
    (my-clause-processor clause
			 '( (:expand (m gamma mu equ-c fdco))
			    (:python-file "delta-rewrite-3")
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
  (implies (and (and (integerp n) (rationalp v0) (rationalp g1))
		(and (>= n 3) (>= v0 9/10) (<= v0 11/10) (equal g1 1/3200)))
	   (equal (delta-2 n v0 g1)
		  (delta-3 n v0 g1)))
  :hints (("Goal"
	   :use ((:instance delta-rewrite-3)))))
)

(defthm delta-rewrite-5
  (implies (and (and (integerp n) (rationalp v0) (rationalp g1))
		(and (>= n 3) (>= v0 9/10) (<= v0 11/10) (equal g1 1/3200)))
	   (equal (delta n v0 g1)
		  (delta-3 n v0 g1)))
  :hints (("Goal"
	   :use ((:instance delta-rewrite-1)
		 (:instance delta-rewrite-2)
		 (:instance delta-rewrite-3)
		 (:instance delta-rewrite-4)))))
)

(encapsulate ()

(local
(defthm delta-<-0-lemma1-lemma
  (implies (and (and (integerp n) (rationalp v0) (rationalp g1))
		(and (>= n 3) (>= v0 9/10) (<= v0 11/10) (equal g1 1/3200)))
	   (implies (< (+ (* (expt (gamma) 2)
			     (- (fdco (1- (m n v0 g1)) v0 g1)
				(fdco (m n v0 g1) v0 g1)))
			  (* (expt (gamma) 1)
			     (- (fdco (m n v0 g1) v0 g1)
				(fdco (1+ (m n v0 g1)) v0 g1)))
			  (* (expt (gamma) (- 2 (* 2 n)))
			     (- (/ (* (mu) (1+ (* *alpha* v0)))
				   (1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0))))) 1))
			  (- (/ (* (mu) (1+ (* *alpha* v0)))
				(1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1))
		       0)
		    (< (* (expt (gamma) (+ -1 n -1 n))
			  (+ (* (expt (gamma) 2)
				(- (fdco (1- (m n v0 g1)) v0 g1)
				   (fdco (m n v0 g1) v0 g1)))
			     (* (expt (gamma) 1)
				(- (fdco (m n v0 g1) v0 g1)
				   (fdco (1+ (m n v0 g1)) v0 g1)))
			     (* (expt (gamma) (- 2 (* 2 n)))
				(- (/ (* (mu) (1+ (* *alpha* v0)))
				      (1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0))))) 1))
			     (- (/ (* (mu) (1+ (* *alpha* v0)))
				   (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1)))
		       0)))
  :hints (("Goal"
	   :clause-processor
	   (my-clause-processor clause
				'( (:expand (m gamma mu equ-c fdco))
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
  (implies (and (and (integerp n) (rationalp v0) (rationalp g1))
		(and (>= n 3) (>= v0 9/10) (<= v0 11/10) (equal g1 1/3200)))
	   (implies (< (delta-3-inside n v0 g1) 0)
		    (< (delta-3 n v0 g1) 0))))
)

(local
(defthm delta-<-0-lemma2-lemma
  (implies (and (and (integerp n) (rationalp v0) (rationalp g1))
		(and (>= n 3) (>= v0 9/10) (<= v0 11/10) (equal g1 1/3200)))
	   (implies (< (/ (+ (* (expt (gamma) 2)
				(- (fdco (1- (m n v0 g1)) v0 g1)
				   (fdco (m n v0 g1) v0 g1)))
			     (* (expt (gamma) 1)
				(- (fdco (m n v0 g1) v0 g1)
				   (fdco (1+ (m n v0 g1)) v0 g1)))
			     (- (/ (* (mu) (1+ (* *alpha* v0)))
				   (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1))
			  (- 1
			     (/ (* (mu) (1+ (* *alpha* v0)))
				(1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0)))))))
		       (expt (gamma) (- 2 (* 2 n))))
		    (< (+ (* (expt (gamma) 2)
			     (- (fdco (1- (m n v0 g1)) v0 g1)
				(fdco (m n v0 g1) v0 g1)))
			  (* (expt (gamma) 1)
			     (- (fdco (m n v0 g1) v0 g1)
				(fdco (1+ (m n v0 g1)) v0 g1)))
			  (* (expt (gamma) (- 2 (* 2 n)))
			     (- (/ (* (mu) (1+ (* *alpha* v0)))
				   (1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0))))) 1))
			  (- (/ (* (mu) (1+ (* *alpha* v0)))
				(1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1))
		       0)))
  :hints (("Goal"
	   :clause-processor
	   (my-clause-processor clause
				'( (:expand (m gamma mu equ-c fdco))
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
  (implies (and (and (integerp n) (rationalp v0) (rationalp g1))
		(and (>= n 3) (>= v0 9/10) (<= v0 11/10) (equal g1 1/3200)))
	   (implies (< (delta-3-inside-transform n v0 g1)
		       (expt (gamma) (- 2 (* 2 n))))
		    (< (delta-3-inside n v0 g1) 0)))
  :hints (("Goal"
	   :use ((:instance delta-<-0-lemma2-lemma)))))
)

(local
;; This is for proving 2n < gamma^(2-2n)
(defthm delta-<-0-lemma3-lemma1
  (implies (and (integerp k)
		(>= k 6))
	   (< k (expt (/ (gamma)) (- k 2)))))
)

(local
(defthm delta-<-0-lemma3-lemma2
  (implies (and (integerp n)
		(>= n 3))
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
  (implies (and (integerp n)
		(>= n 3))
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
  (implies (and (integerp n)
		(>= n 3))
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
  (implies (and (and (integerp n) (rationalp v0) (rationalp g1))
		(and (>= n 3) (>= v0 9/10) (<= v0 11/10) (equal g1 1/3200)))
	   (implies (< (/ (+ (* (expt (gamma) 2)
				(- (fdco (1- (m n v0 g1)) v0 g1)
				   (fdco (m n v0 g1) v0 g1)))
			     (* (expt (gamma) 1)
				(- (fdco (m n v0 g1) v0 g1)
				   (fdco (1+ (m n v0 g1)) v0 g1)))
			     (- (/ (* (mu) (1+ (* *alpha* v0)))
				   (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1))
			  (- 1
			     (/ (* (mu) (1+ (* *alpha* v0)))
				(1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0)))))))
		       (* 2 n))
		    (< (/ (+ (* (expt (gamma) 2)
				(- (fdco (1- (m n v0 g1)) v0 g1)
				   (fdco (m n v0 g1) v0 g1)))
			     (* (expt (gamma) 1)
				(- (fdco (m n v0 g1) v0 g1)
				   (fdco (1+ (m n v0 g1)) v0 g1)))
			     (- (/ (* (mu) (1+ (* *alpha* v0)))
				   (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1))
			  (- 1
			     (/ (* (mu) (1+ (* *alpha* v0)))
				(1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0)))))))
		       (expt (gamma) (- 2 (* 2 n))))))
  :hints (("Goal"
	   :clause-processor
	   (my-clause-processor clause
				'( (:expand (m gamma mu equ-c fdco))
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
  (implies (and (and (integerp n) (rationalp v0) (rationalp g1))
		(and (>= n 3) (>= v0 9/10) (<= v0 11/10) (equal g1 1/3200)))
	   (< (/ (+ (* (expt (gamma) 2)
		       (- (fdco (1- (m n v0 g1)) v0 g1)
			  (fdco (m n v0 g1) v0 g1)))
		    (* (expt (gamma) 1)
		       (- (fdco (m n v0 g1) v0 g1)
			  (fdco (1+ (m n v0 g1)) v0 g1)))
		    (- (/ (* (mu) (1+ (* *alpha* v0)))
			  (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1))
		 (- 1
		    (/ (* (mu) (1+ (* *alpha* v0)))
		       (1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0)))))))
	      (* 2 n)))
  :hints (("Goal"
	   :clause-processor
	   (my-clause-processor clause
				'( (:expand (m gamma mu equ-c fdco))
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
  (implies (and (and (integerp n) (rationalp v0) (rationalp g1))
		(and (>= n 3) (>= v0 9/10) (<= v0 11/10) (equal g1 1/3200)))
	   (< (delta n v0 g1) 0))
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
  (implies (and (rationalp v0)
		(rationalp g1)
		(>= v0 9/10)
		(<= v0 11/10)
		(equal g1 1/3200)
		(integerp n)
		(>= n 3)
		(rationalp phi0)
		(>= phi0 0)
 		(< phi0 (- (fdco (1+ (m n v0 g1)) v0 g1) 1)))
	   (equal (A (+ n 1) phi0 v0 g1)
		  (+ (* (expt (gamma) (+ (* 2 n) 1)) phi0)
		     (* (expt (gamma) (* 2 n))
			(- (fdco (1- (m n v0 g1)) v0 g1) 1))
		     (* (expt (gamma) (- (* 2 n) 1))
			(- (fdco (m n v0 g1) v0 g1) 1))))))
)

(local
(defthm split-phi-2n+1-lemma1-lemma2
  (implies (and (and (integerp n)
		     (rationalp phi0)
		     (rationalp v0)
		     (rationalp g1))
		(and (>= v0 9/10)
		     (<= v0 11/10)
		     (equal g1 1/3200)
		     (>= n 3)
		     (>= phi0 0)
		     (< phi0 (- (fdco (1+ (m n v0 g1)) v0 g1) 1))))
	   (equal (+ (* (expt (gamma) (+ (* 2 n) 1)) phi0)
		     (* (expt (gamma) (* 2 n))
			(- (fdco (1- (m n v0 g1)) v0 g1) 1))
		     (* (expt (gamma) (- (* 2 n) 1))
			(- (fdco (m n v0 g1) v0 g1) 1)))
		  (+ (* (+ (* (expt (gamma) (- (* 2 n) 1)) phi0)
			   (* (expt (gamma) (- (* 2 n) 2))
			      (- (fdco (m n v0 g1) v0 g1) 1))
			   (* (expt (gamma) (- (* 2 n) 3))
			      (- (fdco (1+ (m n v0 g1)) v0 g1) 1)))
			(expt (gamma) 2))
		     (- (* (expt (gamma) (* 2 n))
			   (- (fdco (1- (m n v0 g1)) v0 g1) 1))
			(* (expt (gamma) (* 2 n))
			   (- (fdco (m n v0 g1) v0 g1) 1)))
		     (- (* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (m n v0 g1) v0 g1) 1))
			(* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (1+ (m n v0 g1)) v0 g1) 1))))))
  )
)

(local
(defthm split-phi-2n+1-lemma1-A
  (implies (and (and (integerp n)
		     (rationalp phi0)
		     (rationalp v0)
		     (rationalp g1))
		(and (>= v0 9/10)
		     (<= v0 11/10)
		     (equal g1 1/3200)
		     (>= n 3)
		     (>= phi0 0)
		     (< phi0 (- (fdco (1+ (m n v0 g1)) v0 g1) 1))))
	   (equal (A (+ n 1) phi0 v0 g1)
		  (+ (* (A n phi0 v0 g1) (gamma) (gamma))
		     (- (* (expt (gamma) (* 2 n))
			   (- (fdco (1- (m n v0 g1)) v0 g1) 1))
			(* (expt (gamma) (* 2 n))
			   (- (fdco (m n v0 g1) v0 g1) 1)))
		     (- (* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (m n v0 g1) v0 g1) 1))
			(* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (1+ (m n v0 g1)) v0 g1) 1)))))))
)

(local
(defthm split-phi-2n+1-lemma2-lemma1
  (implies (and (and (integerp n)
		     (rationalp v0)
		     (rationalp g1))
		(and (>= v0 9/10)
		     (<= v0 11/10)
		     (equal g1 1/3200)
		     (>= n 3)))
	   (equal (B (+ n 1) v0 g1)
		  (* (expt (gamma) (- n 1))
		     (B-sum 1 (- n 1) v0 g1)))))
)

(local
(defthm split-phi-2n+1-lemma2-lemma2
  (implies (and (and (integerp n)
		     (rationalp v0)
		     (rationalp g1))
		(and (>= v0 9/10)
		     (<= v0 11/10)
		     (equal g1 1/3200)
		     (>= n 3)))
	   (equal (B (+ n 1) v0 g1)
		  (* (expt (gamma) (- n 1))
		     (+ (B-term (- n 1) v0 g1)
			(B-term (- (- n 1)) v0 g1)
			(B-sum 1 (- n 2) v0 g1))))))
)

(local
(defthm split-phi-2n+1-lemma2-lemma3
  (implies (and (and (integerp n)
		     (rationalp v0)
		     (rationalp g1))
		(and (>= v0 9/10)
		     (<= v0 11/10)
		     (equal g1 1/3200)
		     (>= n 3)))
	   (equal (B (+ n 1) v0 g1)
		  (+ (* (expt (gamma) (- n 1))
			(B-sum 1 (- n 2) v0 g1))
		     (* (expt (gamma) (- n 1))
			(B-term (- n 1) v0 g1))
		     (* (expt (gamma) (- n 1))
			(B-term (- (- n 1)) v0 g1))))))
)

(local
(defthm split-phi-2n+1-lemma2-lemma4
  (implies (and (and (integerp n)
		     (rationalp v0)
		     (rationalp g1))
		(and (>= v0 9/10)
		     (<= v0 11/10)
		     (equal g1 1/3200)
		     (>= n 3)))
	   (equal (B (+ n 1) v0 g1)
		  (+ (* (gamma) (expt (gamma) (- n 2))
			(B-sum 1 (- n 2) v0 g1))
		     (* (expt (gamma) (- n 1))
			(+ (B-term (- n 1) v0 g1)
			   (B-term (- (- n 1)) v0 g1)))))))
)

(local
(defthm split-phi-2n+1-lemma2-lemma5
  (implies (and (and (integerp n)
		     (rationalp v0)
		     (rationalp g1))
		(and (>= v0 9/10)
		     (<= v0 11/10)
		     (equal g1 1/3200)
		     (>= n 3)))
	   (equal (B (+ n 1) v0 g1)
		  (+ (* (gamma) (B n v0 g1))
		     (* (expt (gamma) (- n 1))
			(+ (B-term (- n 1) v0 g1)
			   (B-term (- (- n 1)) v0 g1)))))))
)

(local
(defthm split-phi-2n+1-lemma2-B
  (implies (and (and (integerp n)
		     (rationalp v0)
		     (rationalp g1))
		(and (>= v0 9/10)
		     (<= v0 11/10)
		     (equal g1 1/3200)
		     (>= n 3)))
	   (equal (B (+ n 1) v0 g1)
		  (+ (* (gamma) (B n v0 g1))
		     (* (expt (gamma) (- n 1))
			(+ (* (expt (gamma) (- (- n 1)))
			      (B-term-rest (- n 1) v0 g1))
			   (* (expt (gamma) (- n 1))
			      (B-term-rest (- (- n 1)) v0 g1))))))))
)

(local
(defthm split-phi-2n+1-lemma3-delta-stupidlemma
  (implies (and (and (integerp n)
		     (rationalp v0)
		     (rationalp g1))
		(and (>= v0 9/10)
		     (<= v0 11/10)
		     (equal g1 1/3200)
		     (>= n 3)))
	   (equal (+ (- (* (expt (gamma) (* 2 n))
			   (- (fdco (1- (m n v0 g1)) v0 g1) 1))
			(* (expt (gamma) (* 2 n))
			   (- (fdco (m n v0 g1) v0 g1) 1)))
		     (- (* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (m n v0 g1) v0 g1) 1))
			(* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (1+ (m n v0 g1)) v0 g1) 1)))
		     (* (expt (gamma) (- n 1))
			(+ (* (expt (gamma) (- (- n 1)))
			      (B-term-rest (- n 1) v0 g1))
			   (* (expt (gamma) (- n 1))
			      (B-term-rest (- (- n 1)) v0 g1)))))
		  (+ (- (* (expt (gamma) (* 2 n))
			   (- (fdco (1- (m n v0 g1)) v0 g1) 1))
			(* (expt (gamma) (* 2 n))
			   (- (fdco (m n v0 g1) v0 g1) 1)))
		     (- (* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (m n v0 g1) v0 g1) 1))
			(* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (1+ (m n v0 g1)) v0 g1) 1)))
		     (* (expt (gamma) (1- n))
			(+ (* (expt (gamma) (1+ (- n)))
			      (- (/ (* (mu) (1+ (* *alpha* v0)))
				    (1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0))))) 1))
			   (* (expt (gamma) (1- n))
			      (- (/ (* (mu) (1+ (* *alpha* v0)))
				    (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1))))))))
)

(local
(defthm split-phi-2n+1-lemma3-delta
  (implies (and (and (integerp n)
		     (rationalp v0)
		     (rationalp g1))
		(and (>= v0 9/10)
		     (<= v0 11/10)
		     (equal g1 1/3200)
		     (>= n 3)))
	   (equal (+ (- (* (expt (gamma) (* 2 n))
			   (- (fdco (1- (m n v0 g1)) v0 g1) 1))
			(* (expt (gamma) (* 2 n))
			   (- (fdco (m n v0 g1) v0 g1) 1)))
		     (- (* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (m n v0 g1) v0 g1) 1))
			(* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (1+ (m n v0 g1)) v0 g1) 1)))
		     (* (expt (gamma) (- n 1))
			(+ (* (expt (gamma) (- (- n 1)))
			      (B-term-rest (- n 1) v0 g1))
			   (* (expt (gamma) (- n 1))
			      (B-term-rest (- (- n 1)) v0 g1)))))
		  (delta n v0 g1)))
  :hints (("Goal"
	   :use ((:instance split-phi-2n+1-lemma3-delta-stupidlemma)
		 (:functional-instance (:instance delta)))
	   :in-theory '(minimal-theory))))
)

(local
(defthm split-phi-2n+1-lemma4
  (implies (and (and (integerp n)
		     (rationalp phi0)
		     (rationalp v0)
		     (rationalp g1))
		(and (>= v0 9/10)
		     (<= v0 11/10)
		     (equal g1 1/3200)
		     (>= n 3)
		     (>= phi0 0)
		     (< phi0 (- (fdco (1+ (m n v0 g1)) v0 g1) 1))))
	   (equal (phi-2n-1 (1+ n) phi0 v0 g1)
		  (+ (A (+ n 1) phi0 v0 g1)
		     (B (+ n 1) v0 g1)))))
)

(local
(defthm split-phi-2n+1-lemma5
  (implies (and (and (integerp n)
		     (rationalp phi0)
		     (rationalp v0)
		     (rationalp g1))
		(and (>= v0 9/10)
		     (<= v0 11/10)
		     (equal g1 1/3200)
		     (>= n 3)
		     (>= phi0 0)
		     (< phi0 (- (fdco (1+ (m n v0 g1)) v0 g1) 1))))
	   (equal (phi-2n-1 (1+ n) phi0 v0 g1)
		  (+ (+ (* (A n phi0 v0 g1) (gamma) (gamma))
			(- (* (expt (gamma) (* 2 n))
			      (- (fdco (1- (m n v0 g1)) v0 g1) 1))
			   (* (expt (gamma) (* 2 n))
			      (- (fdco (m n v0 g1) v0 g1) 1)))
			(- (* (expt (gamma) (- (* 2 n) 1))
			      (- (fdco (m n v0 g1) v0 g1) 1))
			   (* (expt (gamma) (- (* 2 n) 1))
			      (- (fdco (1+ (m n v0 g1)) v0 g1) 1))))
		     (+ (* (gamma) (B n v0 g1))
			(* (expt (gamma) (- n 1))
			   (+ (* (expt (gamma) (- (- n 1)))
				 (B-term-rest (- n 1) v0 g1))
			      (* (expt (gamma) (- n 1))
				 (B-term-rest (- (- n 1)) v0 g1))))))))
  :hints (("Goal"
	   :use ((:instance split-phi-2n+1-lemma1-A)
		 (:instance split-phi-2n+1-lemma2-B)))))
)

(local 
(defthm split-phi-2n+1-lemma6
  (implies (and (and (integerp n)
		     (rationalp phi0)
		     (rationalp v0)
		     (rationalp g1))
		(and (>= v0 9/10)
		     (<= v0 11/10)
		     (equal g1 1/3200)
		     (>= n 3)
		     (>= phi0 0)
		     (< phi0 (- (fdco (1+ (m n v0 g1)) v0 g1) 1))))
	   (equal (phi-2n-1 (1+ n) phi0 v0 g1)
		  (+ (* (A n phi0 v0 g1) (gamma) (gamma))
		     (* (gamma) (B n v0 g1))
		     (+ (- (* (expt (gamma) (* 2 n))
			      (- (fdco (1- (m n v0 g1)) v0 g1) 1))
			   (* (expt (gamma) (* 2 n))
			      (- (fdco (m n v0 g1) v0 g1) 1)))
			(- (* (expt (gamma) (- (* 2 n) 1))
			      (- (fdco (m n v0 g1) v0 g1) 1))
			   (* (expt (gamma) (- (* 2 n) 1))
			      (- (fdco (1+ (m n v0 g1)) v0 g1) 1)))
			(* (expt (gamma) (- n 1))
			   (+ (* (expt (gamma) (- (- n 1)))
				 (B-term-rest (- n 1) v0 g1))
			      (* (expt (gamma) (- n 1))
				 (B-term-rest (- (- n 1)) v0 g1)))))))))
)

(defthm split-phi-2n+1
  (implies (and (and (integerp n)
		     (rationalp phi0)
		     (rationalp v0)
		     (rationalp g1))
		(and (>= v0 9/10)
		     (<= v0 11/10)
		     (equal g1 1/3200)
		     (>= n 3)
		     (>= phi0 0)
		     (< phi0 (- (fdco (1+ (m n v0 g1)) v0 g1) 1))))
	   (equal (phi-2n-1 (1+ n) phi0 v0 g1)
 		  (+ (* (gamma) (gamma) (A n phi0 v0 g1)) (* (gamma) (B n v0 g1)) (delta n v0 g1))))
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
				'( (:expand ())
				  (:python-file "except-for-delta-smaller-than-0-lemma1")
				  (:let ())
				  (:hypothesize ())))))
  :rule-classes :linear)
)

(defthm except-for-delta-<-0
  (implies (and (and (integerp n)
		     (rationalp phi0)
		     (rationalp v0)
		     (rationalp g1))
		(and (>= v0 9/10)
		     (<= v0 11/10)
		     (equal g1 1/3200)
		     (>= n 3)
		     (>= phi0 0)
		     (< phi0 (- (fdco (1+ (m n v0 g1)) v0 g1) 1))
		     (< (phi-2n-1 n phi0 v0 g1) 0)))
	   (< (+ (* (gamma) (gamma) (A n phi0 v0 g1))
		 (* (gamma) (B n v0 g1)))
	      0))
  :hints (("Goal"
	   :use ((:instance except-for-delta-<-0-lemma1
			    (c (gamma))
			    (A (A n phi0 v0 g1))
			    (B (B n v0 g1)))
		 (:instance B-neg)))))
)

;; for induction step 
(encapsulate ()
(defthm phi-2n+1-<-0-lemma1
  (implies (and (and (integerp n)
		     (rationalp phi0)
		     (rationalp v0)
		     (rationalp g1))
		(and (>= v0 9/10)
		     (<= v0 11/10)
		     (equal g1 1/3200)
		     (>= n 3)
		     (>= phi0 0)
		     (< phi0 (- (fdco (1+ (m n v0 g1)) v0 g1) 1))
		     (< (phi-2n-1 n phi0 v0 g1) 0)))
	   (< (phi-2n-1 (1+ n) phi0 v0 g1) 0))
  :hints (("Goal"
 	   :use ((:instance split-phi-2n+1)
		 (:instance delta-<-0)
		 (:instance except-for-delta-<-0)))))

(defthm phi-2n+1-<-0
  (implies (and (and (integerp n)
		     (rationalp phi0)
		     (rationalp v0)
		     (rationalp g1))
		(and (>= v0 9/10)
		     (<= v0 11/10)
		     (equal g1 1/3200)
		     (>= n 4)
		     (>= phi0 0)
		     (< phi0 (- (fdco (1+ (m (- n 1) v0 g1)) v0 g1) 1))
		     (< (phi-2n-1 (- n 1) phi0 v0 g1) 0)))
	   (< (phi-2n-1 n phi0 v0 g1) 0))
  :hints (("Goal"
	   :use ((:instance phi-2n+1-<-0-lemma1
			    (n (- n 1)))))))

(defthm phi-2n+1-<-0-corollary-1
  (implies (and (and (integerp n)
		     (rationalp phi0)
		     (rationalp v0)
		     (rationalp g1))
		(and (>= v0 9/10)
		     (<= v0 11/10)
		     (equal g1 1/3200)
		     (>= n 4)
		     (>= phi0 0)
		     (< phi0 (- (fdco (1+ (m (- n 1) v0 g1)) v0 g1) 1))
		     (< (+ (A (- n 1) phi0 v0 g1)
			   (* (expt (gamma) (- (- n 1) 2))
			      (B-sum 1 (- (- n 1) 2) v0 g1)))
			0)))
	   (< (+ (A n phi0 v0 g1)
		 (* (expt (gamma) (- n 2))
		    (B-sum 1 (- n 2) v0 g1)))
	      0))
  :hints (("Goal"
	   :use ((:instance phi-2n+1-<-0)))))

(defthm phi-2n+1-<-0-corollary-2
  (implies (and (integerp n-minus-2)
		(rationalp v0)
		(rationalp g1)
		(rationalp phi0)
		(>= n-minus-2 2)
		(>= v0 9/10)
		(<= v0 11/10)
		(equal g1 1/3200)
		(>= phi0 0)
		(< phi0 (- (fdco (1+ (m (- (+ n-minus-2 2) 1) v0 g1)) v0 g1) 1))
		(< (+ (A (+ n-minus-2 1) phi0 v0 g1)
		      (* (expt (gamma) (- n-minus-2 1))
			 (B-sum 1 (- n-minus-2 1) v0 g1)))
		   0))
	   (< (+ (A (+ n-minus-2 2) phi0 v0 g1)
		 (* (expt (gamma) n-minus-2)
		    (B-sum 1 n-minus-2 v0 g1)))
	      0))
  :hints (("Goal"
	   :use ((:instance phi-2n+1-<-0-corollary-1
			    (n (+ n-minus-2 2)))))))
)

;; CANNOT PROVE
(skip-proofs
(defthm phi-2n-1-<-0-base
  (implies (and (and (integerp n)
		     (rationalp v0)
		     (rationalp g1)
		     (rationalp phi0))
		(and (equal n 3)
		     (>= v0 9/10)
		     (<= v0 11/10)
		     (equal g1 1/3200)
		     (>= phi0 0)
		     (< phi0 (- (fdco (1+ (m n v0 g1)) v0 g1) 1))))
	   (< (phi-2n-1 n phi0 v0 g1) 0))
  :hints (("Goal"
	   :clause-processor
	   (my-clause-processor clause
				'( (:expand (phi-2n-1 m fdco A B B-sum B-term equ-c mu))
				  (:python-file "phi-2n-1-<-0-base")
				  (:let ())
				  (:hypothesize ()))))))
)

;; induction step
(encapsulate ()

;; CANNOT PROVE
(skip-proofs
(defthm phi-2n-1-<-0-inductive-lemma1-lemma1-stupidlemma
  (implies (and (integerp n-minus-2)
		(rationalp v0)
		(rationalp g1)
		(rationalp phi0)
		(equal n-minus-2 1)
		(>= v0 9/10)
		(<= v0 11/10)
		(equal g1 1/3200)
		(>= phi0 0)
		(< phi0 (- (fdco (1+ (m (+ n-minus-2 2) v0 g1)) v0 g1) 1)))
	   (< (+ (A (+ n-minus-2 2) phi0 v0 g1)
		 (* (expt (gamma) n-minus-2)
		    (B-sum 1 n-minus-2 v0 g1))) 0)))
)

(defthm phi-2n-1-<-0-inductive-lemma1-lemma1-lemma1
  (implies (and (and (integerp n_minus_2)
		     (rationalp phi0)
		     (rationalp v0)
		     (rationalp g1))
		(and (<= 1 (+ -1 n_minus_2))
		     (>= v0 9/10)
		     (<= v0 11/10)
		     (equal g1 1/3200)
		     (<= 0 phi0)
		     (< phi0 (+ -1 (fdco (+ 1 (m (+ n_minus_2 2) v0 g1)) v0 g1)))))
	   (and (< phi0 (+ -1 (fdco (+ 1 (m (+ -1 n_minus_2 2) v0 g1)) v0 g1)))
		(> (+ -1 (fdco (+ 1 (m (+ n_minus_2 2) v0 g1)) v0 g1)) 0)
		(> (+ -1 (fdco (+ 1 (m (+ -1 n_minus_2 2) v0 g1)) v0 g1)) 0)))
  :hints (("Goal"
	   :clause-processor
	   (my-clause-processor clause
				'( (:expand (fdco m mu equ-c))
				  (:python-file "phi-2n-1-smaller-than-0-inductive-lemma1-lemma1-lemma1")
				  (:let ())
				  (:hypothesize ()))))))

(defthm phi-2n-1-<-0-inductive-lemma1-lemma1-lemma2
  (implies (integerp n-minus-2)
	   (integerp (+ -1 n-minus-2))))

(defthm phi-2n-1-<-0-inductive-lemma1-lemma1-lemma3-stupidlemma
  (implies (and (implies (and a b c d e f k) g)
		(implies (and a h c d i k) g)
		(implies (and a c b d i k) e)
		(implies a j)
		(and a (or b h))
		(implies (and j b c d e k) f)
		a
		(or b h)
		c
		d
		k
		i)
	   g)
  :rule-classes nil)

(defthm phi-2n-1-<-0-inductive-lemma1-lemma1-lemma3
  (implies (and (implies (and (integerp n-minus-2) ;; a
                            (<= 2 n-minus-2)       ;; b
                            (rationalp phi0)       ;; c
                            (<= 0 phi0)            ;; d
			    (and (rationalp v0)
				 (rationalp g1)
				 (>= v0 9/10)
				 (<= v0 11/10)
				 (equal g1 1/3200)) ;; k
                            (< phi0
                               (+ -1 (fdco (+ 1 (m (+ -1 n-minus-2 2) v0 g1)) v0 g1))) ;; e
                            (< (+ (a (+ n-minus-2 1) phi0 v0 g1)
                                  (* (/ (expt 5 (+ -1 n-minus-2)))
                                     (b-sum 1 (+ -1 n-minus-2) v0 g1)))
                               0))   ;; f
                       (< (+ (a (+ n-minus-2 2) phi0 v0 g1)
                             (* (/ (expt 5 n-minus-2))
                                (b-sum 1 n-minus-2 v0 g1)))
                          0)) ;; g
              (implies (and (integerp n-minus-2) ;; a
                            (equal n-minus-2 1)  ;; h
                            (rationalp phi0) ;; c
			    (and (rationalp v0)
				 (rationalp g1)
				 (>= v0 9/10)
				 (<= v0 11/10)
				 (equal g1 1/3200)) ;; k
                            (<= 0 phi0) ;; d
                            (< phi0
                               (+ -1 (fdco (+ 1 (m (+ n-minus-2 2) v0 g1)) v0 g1)))) ;; i
                       (< (+ (a (+ n-minus-2 2) phi0 v0 g1)
                             (* (/ (expt 5 n-minus-2))
                                (b-sum 1 n-minus-2 v0 g1)))
                          0)) ;; g
              (implies (and (and (integerp n-minus-2) ;; a
                                 (rationalp phi0)) ;; c
                            (<= 1 (+ -1 n-minus-2)) ;; b
			    (and (rationalp v0)
				 (rationalp g1)
				 (>= v0 9/10)
				 (<= v0 11/10)
				 (equal g1 1/3200)) ;; k
                            (<= 0 phi0) ;; d
                            (< phi0
                               (+ -1 (fdco (+ 1 (m (+ n-minus-2 2) v0 g1)) v0 g1)))) ;; i
                       (< phi0
                          (+ -1
                             (fdco (+ 1 (m (+ -1 n-minus-2 2) v0 g1)) v0 g1)))) ;; e
              (implies (integerp n-minus-2) ;; a
                       (integerp (+ -1 n-minus-2))) ;; j
              (not (or (not (integerp n-minus-2))  ;; a
                       (< n-minus-2 1))) ;; (or b h)
              (implies (and (integerp (+ -1 n-minus-2)) ;; j
                            (<= 1 (+ -1 n-minus-2)) ;; b
                            (rationalp phi0) ;; c
			    (and (rationalp v0)
				 (rationalp g1)
				 (>= v0 9/10)
				 (<= v0 11/10)
				 (equal g1 1/3200)) ;; k
                            (<= 0 phi0) ;; d
                            (< phi0
                               (+ -1
                                  (fdco (+ 1 (m (+ -1 n-minus-2 2) v0 g1)) v0 g1)))) ;; e
                       (< (+ (a (+ -1 n-minus-2 2) phi0 v0 g1)
                             (* (/ (expt 5 (+ -1 n-minus-2)))
                                (b-sum 1 (+ -1 n-minus-2) v0 g1)))
                          0)) ;; f
              (integerp n-minus-2) ;;a
              (<= 1 n-minus-2) ;; (or b h)
              (rationalp phi0) ;; c
	      (and (rationalp v0)
		   (rationalp g1)
		   (>= v0 9/10)
		   (<= v0 11/10)
		   (equal g1 1/3200)) ;; k
              (<= 0 phi0) ;; d
              (< phi0
                 (+ -1 (fdco (+ 1 (m (+ n-minus-2 2) v0 g1)) v0 g1)))) ;; i
         (< (+ (a (+ n-minus-2 2) phi0 v0 g1)
               (* (/ (expt 5 n-minus-2))
                  (b-sum 1 n-minus-2 v0 g1)))
            0)) ;; g
  :hints (("Goal"
	   :use ((:instance phi-2n-1-<-0-inductive-lemma1-lemma1-lemma3-stupidlemma
			    (a (integerp n-minus-2))
			    (b (<= 2 n-minus-2))
			    (c (rationalp phi0))
			    (d (<= 0 phi0))
			    (e (< phi0
				  (+ -1
				     (fdco (+ 1 (m (+ -1 n-minus-2 2) v0 g1)) v0 g1))))
			    (f (< (+ (a (+ -1 n-minus-2 2) phi0 v0 g1)
				     (* (/ (expt 5 (+ -1 n-minus-2)))
					(b-sum 1 (+ -1 n-minus-2) v0 g1)))
				  0))
			    (g (< (+ (a (+ n-minus-2 2) phi0 v0 g1)
				     (* (/ (expt 5 n-minus-2))
					(b-sum 1 n-minus-2 v0 g1)))
				  0))
			    (h (equal n-minus-2 1))
			    (i (< phi0
				  (+ -1 (fdco (+ 1 (m (+ n-minus-2 2) v0 g1)) v0 g1))))
			    (j (integerp (+ -1 n-minus-2)))
			    (k (and (rationalp v0)
				 (rationalp g1)
				 (>= v0 9/10)
				 (<= v0 11/10)
				 (equal g1 1/3200)))))))
  )

(defthm phi-2n-1-<-0-inductive-lemma1-lemma1
  (implies (and (integerp n-minus-2)
		(rationalp v0)
		(rationalp g1)
		(rationalp phi0)
		(>= n-minus-2 1)
		(>= v0 9/10)
		(<= v0 11/10)
		(equal g1 1/3200)
		(>= phi0 0)
		(< phi0 (- (fdco (1+ (m (+ n-minus-2 2) v0 g1)) v0 g1) 1)))
	   (< (+ (A (+ n-minus-2 2) phi0 v0 g1)
		 (* (expt (gamma) n-minus-2)
		    (B-sum 1 n-minus-2 v0 g1))) 0))
  :hints (("Goal"
	   :do-not '(simplify)
	   :induct (B-sum 1 n-minus-2 v0 g1)
	   :in-theory (disable fdco m))
	  ("Subgoal *1/'"
	   :use ((:instance phi-2n+1-<-0-corollary-2)
		 (:instance phi-2n-1-<-0-inductive-lemma1-lemma1-stupidlemma)
		 (:instance phi-2n-1-<-0-inductive-lemma1-lemma1-lemma1
			    (n_minus_2 n-minus-2))
		 (:instance phi-2n-1-<-0-inductive-lemma1-lemma1-lemma2)
		 (:instance phi-2n-1-<-0-inductive-lemma1-lemma1-lemma3)
		 )
	   :in-theory (disable phi-2n+1-<-0-corollary-2
			       phi-2n-1-<-0-inductive-lemma1-lemma1-stupidlemma
			       phi-2n-1-<-0-inductive-lemma1-lemma1-lemma1
			       phi-2n-1-<-0-inductive-lemma1-lemma1-lemma2
			       phi-2n-1-<-0-inductive-lemma1-lemma1-lemma3
			       fdco m))
	  ))

(defthm phi-2n-1-<-0-inductive-lemma1
  (implies (and (integerp n)
		(and (rationalp v0)
		     (rationalp g1)
		     (>= v0 9/10)
		     (<= v0 11/10)
		     (equal g1 1/3200))
		(>= n 3)
		(rationalp phi0)
		(>= phi0 0)
		(< phi0 (- (fdco (1+ (m n v0 g1)) v0 g1) 1)))
	   (< (+ (A n phi0 v0 g1)
		 (* (expt (gamma) (- n 2))
		    (B-sum 1 (- n 2) v0 g1))) 0))
  :hints (("Goal"
	   :use ((:instance phi-2n-1-<-0-inductive-lemma1-lemma1
			    (n-minus-2 (- n 2)))))))

(defthm phi-2n-1-<-0-inductive-lemma2
  (implies (and (integerp n)
		(and (rationalp v0)
		     (rationalp g1)
		     (>= v0 9/10)
		     (<= v0 11/10)
		     (equal g1 1/3200))
		(>= n 3)
		(rationalp phi0)
		(>= phi0 0)
		(< phi0 (- (fdco (1+ (m n v0 g1)) v0 g1) 1)))
	   (< (+ (A n phi0 v0 g1) (B n v0 g1)) 0))
  :hints (("Goal"
	   :use ((:instance phi-2n-1-<-0-inductive-lemma1)))))

(defthm phi-2n-1-<-0-inductive
  (implies (and (integerp n)
		(and (rationalp v0)
		     (rationalp g1)
		     (>= v0 9/10)
		     (<= v0 11/10)
		     (equal g1 1/3200))
		(>= n 3)
		(rationalp phi0)
		(>= phi0 0)
		(< phi0 (- (fdco (1+ (m n v0 g1)) v0 g1) 1)))
	   (< (phi-2n-1 n phi0 v0 g1) 0))
  :hints (("Goal"
	   :use ((:instance phi-2n-1-<-0-inductive-lemma2)))))
)

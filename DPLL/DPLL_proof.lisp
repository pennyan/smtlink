(in-package "ACL2")
(include-book "global")
(include-book "arithmetic/top-with-meta" :dir :system)

;; for the clause processor to work
(include-book "../smtlink/SMT-connect")
(logic)
:set-state-ok t
:set-ignore-ok t

(defun fdco (n)
  (/ (* (mu) (+ 1 (* *alpha* *v0*))) (+ 1 (* *beta* n *g1*))))

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
			    (:python-file "B-term-neg-lemma3") ;;mktemp
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

(defun A (n phi0)
  (+ (* (expt (gamma) (- (* 2 n) 1)) phi0)
     (* (expt (gamma) (- (* 2 n) 2))
	(- (fdco (m n)) 1))
     (* (expt (gamma) (- (* 2 n) 3))
	(- (fdco (1+ (m n))) 1))))

(defun phi-2n-1 (n phi0)
  (+ (A n phi0) (B n)))

(defun delta (n)
  (+ (- (* (expt (gamma) (* 2 n))
	   (- (fdco (1- (m n))) 1))
	(* (expt (gamma) (* 2 n))
	   (- (fdco (m n)) 1)))
     (- (* (expt (gamma) (- (* 2 n) 1))
	   (- (fdco (m n)) 1))
	(* (expt (gamma) (- (* 2 n) 1))
	   (- (fdco (1+ (m n))) 1)))
     (* (expt (gamma) (1- n))
	(+ (* (expt (gamma) (1+ (- n)))
	      (- (/ (* (mu) (1+ (* *alpha* *v0*)))
		    (1+ (* *beta* (+ (* *g1* (1- n)) (equ-c)))))
		 1))
	   (* (expt (gamma) (1- n))
	      (- (/ (* (mu) (1+ (* *alpha* *v0*)))
		    (1+ (* *beta* (+ (* *g1* (- 1 n)) (equ-c)))))
		 1))))))

(defun delta-1 (n)
  (+ (* (expt (gamma) (* 2 n))
	(- (fdco (1- (m n)))
	   (fdco (m n))))
     (* (expt (gamma) (- (* 2 n) 1))
	(- (fdco (m n))
	   (fdco (1+ (m n)))))
     (* (* (expt (gamma) (1- n)) (expt (gamma) (1+ (- n))))
	(- (/ (* (mu) (1+ (* *alpha* *v0*)))
	      (1+ (* *beta* (+ (* *g1* (1- n)) (equ-c))))) 1))
     (* (* (expt (gamma) (1- n)) (expt (gamma) (1- n)))
	(- (/ (* (mu) (1+ (* *alpha* *v0*)))
	      (1+ (* *beta* (+ (* *g1* (- 1 n)) (equ-c))))) 1))))

(defun delta-2 (n)
  (+ (* (expt (gamma) (* 2 n))
	(- (fdco (1- (m n)))
	   (fdco (m n))))
     (* (expt (gamma) (- (* 2 n) 1))
	(- (fdco (m n))
	   (fdco (1+ (m n)))))
     (- (/ (* (mu) (1+ (* *alpha* *v0*)))
	   (1+ (* *beta* (+ (* *g1* (1- n)) (equ-c))))) 1)
     (* (expt (gamma) (+ -1 n -1 n))
	(- (/ (* (mu) (1+ (* *alpha* *v0*)))
	      (1+ (* *beta* (+ (* *g1* (- 1 n)) (equ-c))))) 1))))

(defun delta-3 (n)
  (* (expt (gamma) (+ -1 n -1 n))
     (+ (* (expt (gamma) 2)
	   (- (fdco (1- (m n)))
	      (fdco (m n))))
	(* (expt (gamma) 1)
	   (- (fdco (m n))
	      (fdco (1+ (m n)))))
	(* (expt (gamma) (- 2 (* 2 n)))
	   (- (/ (* (mu) (1+ (* *alpha* *v0*)))
		 (1+ (* *beta* (+ (* *g1* (1- n)) (equ-c))))) 1))
	(- (/ (* (mu) (1+ (* *alpha* *v0*)))
	      (1+ (* *beta* (+ (* *g1* (- 1 n)) (equ-c))))) 1))))

(defun delta-3-inside (n)
  (+ (* (expt (gamma) 2)
	   (- (fdco (1- (m n)))
	      (fdco (m n))))
	(* (expt (gamma) 1)
	   (- (fdco (m n))
	      (fdco (1+ (m n)))))
	(* (expt (gamma) (- 2 (* 2 n)))
	   (- (/ (* (mu) (1+ (* *alpha* *v0*)))
		 (1+ (* *beta* (+ (* *g1* (1- n)) (equ-c))))) 1))
	(- (/ (* (mu) (1+ (* *alpha* *v0*)))
	      (1+ (* *beta* (+ (* *g1* (- 1 n)) (equ-c))))) 1)))

(defun delta-3-inside-transform (n)
  (/ 
   (+ (* (expt (gamma) 2)
	 (- (fdco (1- (m n)))
	    (fdco (m n))))
      (* (expt (gamma) 1)
	 (- (fdco (m n))
	    (fdco (1+ (m n)))))
      (- (/ (* (mu) (1+ (* *alpha* *v0*)))
	    (1+ (* *beta* (+ (* *g1* (- 1 n)) (equ-c))))) 1))
   (- 1
      (/ (* (mu) (1+ (* *alpha* *v0*)))
	 (1+ (* *beta* (+ (* *g1* (1- n)) (equ-c))))))))

;; rewrite delta term
(encapsulate ()

;; considering using smtlink for the proof, probably simpler
(defthm delta-rewrite-1-lemma1
  (implies (and (integerp n)
		(>= n 4))
	   (equal (+ (- (* (expt (gamma) (* 2 n))
			   (- (fdco (1- (m n))) 1))
			(* (expt (gamma) (* 2 n))
			   (- (fdco (m n)) 1)))
		     (- (* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (m n)) 1))
			(* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (1+ (m n))) 1)))
		     (* (expt (gamma) (1- n))
			(+ (* (expt (gamma) (1+ (- n)))
			      (- (/ (* (mu) (1+ (* *alpha* *v0*)))
				    (1+ (* *beta* (+ (* *g1* (1- n)) (equ-c)))))
				 1))
			   (* (expt (gamma) (1- n))
			      (- (/ (* (mu) (1+ (* *alpha* *v0*)))
				    (1+ (* *beta* (+ (* *g1* (- 1 n)) (equ-c)))))
				 1)))))
		    (+ (* (expt (gamma) (* 2 n))
			  (- (fdco (1- (m n)))
			     (fdco (m n))))
		       (* (expt (gamma) (- (* 2 n) 1))
			  (- (fdco (m n))
			     (fdco (1+ (m n)))))
		       (* (* (expt (gamma) (1- n)) (expt (gamma) (1+ (- n))))
			  (- (/ (* (mu) (1+ (* *alpha* *v0*)))
				(1+ (* *beta* (+ (* *g1* (1- n)) (equ-c))))) 1))
		       (* (* (expt (gamma) (1- n)) (expt (gamma) (1- n)))
			  (- (/ (* (mu) (1+ (* *alpha* *v0*)))
				(1+ (* *beta* (+ (* *g1* (- 1 n)) (equ-c))))) 1)))))
  :hints
  (("Goal"
    :clause-processor
    (my-clause-processor clause
			 '( (:expand (m gamma mu equ-c fdco))
			    (:python-file "delta-rewrite-1") ;;mktemp
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

(defthm delta-rewrite-1
  (implies (and (integerp n)
		(>= n 4))
	   (equal (delta n)
		  (delta-1 n))))

(defthm delta-rewrite-2-lemma1
  (implies (and (integerp n)
		(>= n 4))
	   (equal (* (expt (gamma) (1- n))
		     (expt (gamma) (1+ (- n))))
		  1))
  :hints (("Goal"
	   :use ((:instance expt-minus
			    (r (gamma))
			    (i (- (1+ (- n)))))))))

(defthm delta-rewrite-2-lemma2
  (implies (and (integerp n)
		(>= n 4))
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

(defthm delta-rewrite-2-lemma3
  (implies (and (integerp n)
		(>= n 4))
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

(defthm delta-rewrite-2
  (implies (and (integerp n)
		(>= n 4))
	   (equal (delta-1 n)
		  (delta-2 n)))
  :hints (("Goal"
	   :use ((:instance delta-rewrite-2-lemma3
			    (A (* (expt (gamma) (* 2 n))
				  (- (fdco (1- (m n)))
				     (fdco (m n)))))
			    (B (* (expt (gamma) (- (* 2 n) 1))
				  (- (fdco (m n))
				     (fdco (1+ (m n))))))
			    (C (- (/ (* (mu) (1+ (* *alpha* *v0*)))
				     (1+ (* *beta* (+ (* *g1* (1- n)) (equ-c))))) 1))
			    (D (- (/ (* (mu) (1+ (* *alpha* *v0*)))
				     (1+ (* *beta* (+ (* *g1* (- 1 n)) (equ-c))))) 1)))))))

(defthm delta-rewrite-3-lemma1-lemma1
  (implies (and (integerp n)
		(>= n 4))
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

(defthm delta-rewrite-3-lemma1-stupidlemma
  (implies (and (integerp n)
		(>= n 4))
	   (equal (* 2 n) (+ (+ -1 n -1 n) 2))))

(defthm delta-rewrite-3-lemma1
  (implies (and (integerp n)
		(>= n 4))
	   (equal (expt (gamma) (* 2 n))
		  (* (expt (gamma) (+ -1 n -1 n))
		     (expt (gamma) 2)))))

(defthm delta-rewrite-3-lemma2-lemma1
  (implies (and (integerp n)
		(>= n 4))
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

(defthm delta-rewrite-3-lemma2-stupidlemma
  (implies (and (integerp n)
		(>= n 4))
	   (equal (- (* 2 n) 1) (+ (+ -1 n -1 n) 1))))

(defthm delta-rewrite-3-lemma2
  (implies (and (integerp n)
		(>= n 4))
	   (equal (expt (gamma) (- (* 2 n) 1))
		  (* (expt (gamma) (+ -1 n -1 n))
		     (expt (gamma) 1))))
  :hints (("Goal"
	   :use ((:instance delta-rewrite-3-lemma2-lemma1)
		 (:instance delta-rewrite-3-lemma2-stupidlemma))
	   :in-theory (disable delta-rewrite-2-lemma1))))

(defthm delta-rewrite-3-lemma3
  (implies (and (integerp n)
		(>= n 4))
	   (equal (* (expt (gamma) (- 2 (* 2 n)))
		     (expt (gamma) (+ -1 n -1 n)))
		  1))
  :hints (("Goal"
	   :use ((:instance expt-minus
			    (r (gamma))
			    (i (- (- 2 (* 2 n)))))))))

(skip-proofs
(defthm delta-rewrite-3
  (implies (and (integerp n)
		(>= n 4))
	   (equal (+ (* (expt (gamma) (* 2 n))
			(- (fdco (1- (m n)))
			   (fdco (m n))))
		     (* (expt (gamma) (- (* 2 n) 1))
			(- (fdco (m n))
			   (fdco (1+ (m n)))))
		     (- (/ (* (mu) (1+ (* *alpha* *v0*)))
			   (1+ (* *beta* (+ (* *g1* (1- n)) (equ-c))))) 1)
		     (* (expt (gamma) (+ -1 n -1 n))
			(- (/ (* (mu) (1+ (* *alpha* *v0*)))
			      (1+ (* *beta* (+ (* *g1* (- 1 n)) (equ-c))))) 1)))
		  (* (expt (gamma) (+ -1 n -1 n))
		     (+ (* (expt (gamma) 2)
			   (- (fdco (1- (m n)))
			      (fdco (m n))))
			(* (expt (gamma) 1)
			   (- (fdco (m n))
			      (fdco (1+ (m n)))))
			(* (expt (gamma) (- 2 (* 2 n)))
			   (- (/ (* (mu) (1+ (* *alpha* *v0*)))
				 (1+ (* *beta* (+ (* *g1* (1- n)) (equ-c))))) 1))
			(- (/ (* (mu) (1+ (* *alpha* *v0*)))
			      (1+ (* *beta* (+ (* *g1* (- 1 n)) (equ-c))))) 1)))))
  :hints
  (("Goal"
    :do-not '(simplify)
    :in-theory (disable delta-rewrite-2-lemma1)
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
					   (equal 1
					  	  (* expt_gamma_2n_minus_2 expt_gamma_2_minus_2n)))
			     ))))))
)

(defthm delta-rewrite-4
  (implies (and (integerp n)
		(>= n 4))
	   (equal (delta-2 n)
		  (delta-3 n)))
  :hints (("Goal"
	   :use ((:instance delta-rewrite-3)))))

(defthm delta-rewrite-5
  (implies (and (integerp n)
		(>= n 4))
	   (equal (delta n)
		  (delta-3 n)))
  :hints (("Goal"
	   :use ((:instance delta-rewrite-1)
		 (:instance delta-rewrite-2)
		 (:instance delta-rewrite-3)
		 (:instance delta-rewrite-4)))))
)

(encapsulate ()

(defthm delta-<-0-lemma1-lemma
  (implies (and (integerp n)
		(>= n 4))
	   (implies (< (+ (* (expt (gamma) 2)
			     (- (fdco (1- (m n)))
				(fdco (m n))))
			  (* (expt (gamma) 1)
			     (- (fdco (m n))
				(fdco (1+ (m n)))))
			  (* (expt (gamma) (- 2 (* 2 n)))
			     (- (/ (* (mu) (1+ (* *alpha* *v0*)))
				   (1+ (* *beta* (+ (* *g1* (1- n)) (equ-c))))) 1))
			  (- (/ (* (mu) (1+ (* *alpha* *v0*)))
				(1+ (* *beta* (+ (* *g1* (- 1 n)) (equ-c))))) 1))
		       0)
		    (< (* (expt (gamma) (+ -1 n -1 n))
			  (+ (* (expt (gamma) 2)
				(- (fdco (1- (m n)))
				   (fdco (m n))))
			     (* (expt (gamma) 1)
				(- (fdco (m n))
				   (fdco (1+ (m n)))))
			     (* (expt (gamma) (- 2 (* 2 n)))
				(- (/ (* (mu) (1+ (* *alpha* *v0*)))
				      (1+ (* *beta* (+ (* *g1* (1- n)) (equ-c))))) 1))
			     (- (/ (* (mu) (1+ (* *alpha* *v0*)))
				   (1+ (* *beta* (+ (* *g1* (- 1 n)) (equ-c))))) 1)))
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

(defthm delta-<-0-lemma1
  (implies (and (integerp n)
		(>= n 4))
	   (implies (< (delta-3-inside n) 0)
		    (< (delta-3 n) 0))))

(defthm delta-<-0-lemma2-lemma
  (implies (and (integerp n)
		(>= n 4))
	   (implies (< (/ (+ (* (expt (gamma) 2)
				(- (fdco (1- (m n)))
				   (fdco (m n))))
			     (* (expt (gamma) 1)
				(- (fdco (m n))
				   (fdco (1+ (m n)))))
			     (- (/ (* (mu) (1+ (* *alpha* *v0*)))
				   (1+ (* *beta* (+ (* *g1* (- 1 n)) (equ-c))))) 1))
			  (- 1
			     (/ (* (mu) (1+ (* *alpha* *v0*)))
				(1+ (* *beta* (+ (* *g1* (1- n)) (equ-c)))))))
		       (expt (gamma) (- 2 (* 2 n))))
		    (< (+ (* (expt (gamma) 2)
			     (- (fdco (1- (m n)))
				(fdco (m n))))
			  (* (expt (gamma) 1)
			     (- (fdco (m n))
				(fdco (1+ (m n)))))
			  (* (expt (gamma) (- 2 (* 2 n)))
			     (- (/ (* (mu) (1+ (* *alpha* *v0*)))
				   (1+ (* *beta* (+ (* *g1* (1- n)) (equ-c))))) 1))
			  (- (/ (* (mu) (1+ (* *alpha* *v0*)))
				(1+ (* *beta* (+ (* *g1* (- 1 n)) (equ-c))))) 1))
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

(defthm delta-<-0-lemma2
  (implies (and (integerp n)
		(>= n 4))
	   (implies (< (delta-3-inside-transform n)
		       (expt (gamma) (- 2 (* 2 n))))
		    (< (delta-3-inside n) 0)))
  :hints (("Goal"
	   :use ((:instance delta-<-0-lemma2-lemma)))))

(skip-proofs
(defthm delta-<-0-lemma3
  (implies (and (integerp n)
		(>= n 4))
	   (implies (< (/ (+ (* (expt (gamma) 2)
				(- (fdco (1- (m n)))
				   (fdco (m n))))
			     (* (expt (gamma) 1)
				(- (fdco (m n))
				   (fdco (1+ (m n)))))
			     (- (/ (* (mu) (1+ (* *alpha* *v0*)))
				   (1+ (* *beta* (+ (* *g1* (- 1 n)) (equ-c))))) 1))
			  (- 1
			     (/ (* (mu) (1+ (* *alpha* *v0*)))
				(1+ (* *beta* (+ (* *g1* (1- n)) (equ-c)))))))
		       (* 2 n))
		    (< (/ (+ (* (expt (gamma) 2)
				(- (fdco (1- (m n)))
				   (fdco (m n))))
			     (* (expt (gamma) 1)
				(- (fdco (m n))
				   (fdco (1+ (m n)))))
			     (- (/ (* (mu) (1+ (* *alpha* *v0*)))
				   (1+ (* *beta* (+ (* *g1* (- 1 n)) (equ-c))))) 1))
			  (- 1
			     (/ (* (mu) (1+ (* *alpha* *v0*)))
				(1+ (* *beta* (+ (* *g1* (1- n)) (equ-c)))))))
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
				  (:hypothesize ((< (* 2 n) expt_gamma_2_minus_2n))))))))
)

(defthm delta-<-0-lemma4
  (implies (and (integerp n)
		(>= n 4))
	   (< (/ (+ (* (expt (gamma) 2)
		       (- (fdco (1- (m n)))
			  (fdco (m n))))
		    (* (expt (gamma) 1)
		       (- (fdco (m n))
			  (fdco (1+ (m n)))))
		    (- (/ (* (mu) (1+ (* *alpha* *v0*)))
			  (1+ (* *beta* (+ (* *g1* (- 1 n)) (equ-c))))) 1))
		 (- 1
		    (/ (* (mu) (1+ (* *alpha* *v0*)))
		       (1+ (* *beta* (+ (* *g1* (1- n)) (equ-c)))))))
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
				  (:hypothesize ()))))))

(defthm delta-<-0
  (implies (and (integerp n)
		(>= n 4))
	   (< (delta n) 0))
  :hints (("Goal"
	   :use ((:instance delta-rewrite-5)
		 (:instance delta-<-0-lemma4)
		 (:instance delta-<-0-lemma3)
		 (:instance delta-<-0-lemma2)
		 (:instance delta-<-0-lemma1)))))
) ;; delta < 0 thus is proved

(encapsulate ()

(defthm split-phi-2n+1-lemma1-lemma1
  (implies (and (integerp n)
		(>= n 4)
		(>= phi0 0)
 		(< phi0 (- (fdco (1+ (m n))) 1)))
	   (equal (A (+ n 1) phi0)
		  (+ (* (expt (gamma) (+ (* 2 n) 1)) phi0)
		     (* (expt (gamma) (* 2 n))
			(- (fdco (1- (m n))) 1))
		     (* (expt (gamma) (- (* 2 n) 1))
			(- (fdco (m n)) 1))))))

(defthm split-phi-2n+1-lemma1-lemma2
  (implies (and (integerp n)
		(>= n 4)
		(>= phi0 0)
 		(< phi0 (- (fdco (1+ (m n))) 1)))
	   (equal (+ (* (expt (gamma) (+ (* 2 n) 1)) phi0)
		     (* (expt (gamma) (* 2 n))
			(- (fdco (1- (m n))) 1))
		     (* (expt (gamma) (- (* 2 n) 1))
			(- (fdco (m n)) 1)))
		  (+ (* (+ (* (expt (gamma) (- (* 2 n) 1)) phi0)
			   (* (expt (gamma) (- (* 2 n) 2))
			      (- (fdco (m n)) 1))
			   (* (expt (gamma) (- (* 2 n) 3))
			      (- (fdco (1+ (m n))) 1)))
			(expt (gamma) 2))
		     (- (* (expt (gamma) (* 2 n))
			   (- (fdco (1- (m n))) 1))
			(* (expt (gamma) (* 2 n))
			   (- (fdco (m n)) 1)))
		     (- (* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (m n)) 1))
			(* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (1+ (m n))) 1))))))
  :hints (("Goal"
	   :hints (("Goal"
	   :clause-processor
	   (my-clause-processor clause
				'( (:expand (m gamma mu equ-c fdco))
				  (:python-file "delta-smaller-than-0-lemma4")
				  (:let ((expt_gamma_2n_plus_1
					  (expt (gamma) (+ (* 2 n) 1))
					   rationalp)
					 (expt_gamma_2n
					  (expt (gamma) (* 2 n))
					   rationalp)
					 (expt_gamma_2n_minus_1
					  (expt (gamma) (- (* 2 n) 1))
					   rationalp)
					 (expt_gamma_2n_minus_2
					  (expt (gamma) (- (* 2 n) 2))
					   rationalp)
					 (expt_gamma_2n_minus_3
					  (expt (gamma) (- (* 2 n) 3))
					   rationalp)
					 (expt_gamma_2
					  (expt (gamma) 2)
					   rationalp)))
				  (:hypothesize ()))))))))

(defthm split-phi-2n+1-lemma1
  (implies (and (integerp n)
		(>= n 4)
		(>= phi0 0)
 		(< phi0 (- (fdco (1+ (m n))) 1)))
	   (equal (A (+ n 1) phi0)
		  (+ (* (A n phi0) (gamma) (gamma))
		     (- (* (expt (gamma) (* 2 n))
			   (- (fdco (1- (m n))) 1))
			(* (expt (gamma) (* 2 n))
			   (- (fdco (m n)) 1)))
		     (- (* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (m n)) 1))
			(* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (1+ (m n))) 1))))))
  )

(skip-proofs
(defthm split-phi-2n+1
  (implies (and (integerp n)
 		(>= n 4)
 		(>= phi0 0)
 		(< phi0 (- (fdco (1+ (m n))) 1)))
	   (equal (phi-2n-1 (1+ n) phi0)
 		  (+ (* (gamma) (gamma) (A n phi0)) (* (gamma) (B n)) (delta n)))))
)

)

(defthm split-phi-2n-1
  (implies (and (integerp n)
 		(>= n 4)
 		(>= phi0 0)
 		(< phi0 (- (fdco (1+ (m n))) 1)))
	   (equal (phi-2n-1 n phi0)
		  (+ (A n phi0) (B n)))))

(skip-proofs
(defthm phi-2n+1-<-0
  (implies (and (integerp n)
		(>= n 4)
		(>= phi0 0)
		(< phi0 (- (/ (* (mu) (+ 1 (* *alpha* *v0*))) (+ 1 (* *beta* (1+ (m n)) *g1*))) 1))
		(< (phi-2n-1 n phi0) 0))
	   (< (phi-2n-1 (1+ n) phi0) 0))
  :hints (("Goal"
 	   :use ((:instance delta-<-0)
		 (:instance split-phi-2n+1)
 		 (:instance split-phi-2n-1)))))
)

(defthm phi-2n-1-<-0-3
  (implies (and (integerp n)
		(equal n 3)
		(>= phi0 0)
		(< phi0 (- (/ (* (mu) (+ 1 (* *alpha* *v0*))) (+ 1 (* *beta* (1+ (m n)) *g1*))) 1)))
	   (< (phi-2n-1 n phi0) 0)))

(skip-proofs
(defthm phi-2n-1-<-0
  (implies (and (integerp n)
		(>= n 4)
		(<= n 320)
		(>= phi0 0)
		(< phi0 (- (/ (* (mu) (+ 1 (* *alpha* *v0*))) (+ 1 (* *beta* (1+ (m n)) *g1*))) 1)))
	   (< (phi-2n-1 n phi0) 0))
  :hints (("Goal"

	   :use ((:instance phi-2n-1-<-0-3)
		 (:instance phi-2n+1-<-0))
	   ))))

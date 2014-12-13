;; This file proves convergence rate of gradient descent
;; on a quadratic function

(in-package "ACL2")
(ld "basics.lisp")
(include-book "arithmetic/top-with-meta" :dir :system)

;; ;; set current book directory to the acl2 book directory
;; :set-cbd "/ubc/cs/research/isd/users/software/ACL2/acl2-sources/books"

;; set up directories to book
;;     books/workshops/2003/cowles-gamboa-van-baalen_matrix/
;;(encapsulate ()
  ;; (add-include-book-dir :matrix "workshops/2003/cowles-gamboa-van-baalen_matrix/support")
 ;; (local
 ;;  (include-book "matrix" :dir :matrix)
 ;;  )

 ;;(local
 ;; define function f
 (defun f (x A b c)
   "f(x) = 1/2 x^TAx - b^Tx + c"
   (m-+ (m-* (m-trans x) A x)
	(m-- (m-trans b) x)
	c))
 ;;)
 
 ;;(local
 (defun f-p (x A b)
   "f'(x) = Ax - b"
   (m-- (m-* A x) b))
 ;;)
 
 ;;(local
 (defun f-pp (A)
   "f''(x) = A"
   A)
 ;;)
 
 ;;(local
 (defun inc-x (x-k alpha-k gradient)
   "x^{k+1} = x^{k} - alpha_k*f'(x^k)"
   (m-- x-k (s-* alpha-k gradient))
   )
 ;;)

 ;; rewrite rule 1
 ;; ||x^k+1 - x^*|| = ||x^k - alpha_k*f'(x^k) - x^*||
 ;;(local
 (defthm rewrite-1
     (implies (and ;; Declare variables
	           ;; matrix A
	           (alist2p 'A A)
		   ;; vector b, x^k, x^k+1, x^*
		   (alist2p 'b b)
		   (alist2p 'x^k x^k)
		   (alist2p 'x^k+1 x^k+1)
		   (alist2p 'x^* x^*)
		   ;; declare iteration step size
		   (realp alpha-k)
		   ;; define iteration update function
		   (equal x^k+1 (m-- x^k (s-* alpha-k (f-p x^k A b))))
		   )
	      (equal
	       (v-2norm (m-- x^k+1 x^*))
	       (v-2norm (m-- (m-- x^k (s-* alpha-k (f-p x^k A b))) x^*))
	       ))
   :hints (("Goal"
	    :use ((:instance inc-x))
	    :in-theory '(minimal-theory)
	    ))
   :rule-classes nil)
 ;;)

  ;; rewrite rule 2
 ;; ||x^k - alpha_k*f'(x^k) - x^*|| = ||x^k - alpha_k*(Ax^k-b) - x^*||
 ;;(local
 (defthm rewrite-2
   (implies (and (alist2p 'A A)
		 (alist2p 'b b)
		 (alist2p 'x^k x^k)
		 (alist2p 'x^* x^*)
		 (realp alpha-k)
		 )
	    (equal
	     (v-2norm (m-- (m-- x^k (s-* alpha-k (f-p x^k A b))) x^*))
	     (v-2norm (m-- (m-- x^k (s-* alpha-k (m-- (m-* A x^k) b))) x^*))
	     ))
   :hints (("Goal"
	    :use ((:instance f-p))
	    ))
   :rule-classes nil)
 ;;)

(defthm rewrite-2-corollary
   (implies (and (alist2p 'A A)
		 (alist2p 'b b)
		 (alist2p 'x^k x^k)
		 (alist2p 'x^k+1 x^k+1)
		 (alist2p 'x^* x^*)
		 (realp alpha-k)
		 (equal x^k+1 (m-- x^k (s-* alpha-k (f-p x^k A b))))
		 )
	    (equal
	     (v-2norm (m-- x^k+1 x^*))
	     (v-2norm (m-- (m-- x^k (s-* alpha-k (m-- (m-* A x^k) b))) x^*))
	     ))
   :hints (("Goal"
	    :use ((:instance rewrite-1)
		  (:instance rewrite-2)
		  (:instance m-=-transitivity))
	    ))
   :rule-classes nil)

 ;; rewrite rule 3
 ;; ||x^k - alpha_k*(Ax^k-b) - x^*|| = ||(x^k - x^*) - alpha_k*(Ax^k-b)||
 ;;(local
 (defthm rewrite-3
   (implies (and (alist2p 'A A)
		 (alist2p 'b b)
		 (alist2p 'x^k x^k)
		 (alist2p 'x^* x^*)
		 (realp alpha-k)
		 )
	    (equal
	     (v-2norm (m-- (m-- x^k (s-* alpha-k (m-- (m-* A x^k) b))) x^*))
	     (v-2norm (m-- (m-- x^k x^*) (s-* alpha-k (m-- (m-* A x^k) b))))
	     ))
   :rule-classes nil)
 ;;)

 (defthm rewrite-3-corollary
   (implies (and (alist2p 'A A)
		 (alist2p 'b b)
		 (alist2p 'x^k x^k)
		 (alist2p 'x^k+1 x^k+1)
		 (alist2p 'x^* x^*)
		 (realp alpha-k)
		 (equal x^k+1 (m-- x^k (s-* alpha-k (f-p x^k A b))))
		 )
	    (equal
	     (v-2norm (m-- x^k+1 x^*))
	     (v-2norm (m-- (m-- x^k x^*) (s-* alpha-k (m-- (m-* A x^k) b))))
	     ))
   :hints (("Goal"
	    :use ((:instance rewrite-2-corollary)
		  (:instance rewrite-3)
		  (:instance m-=-transitivity))
	    ))
   :rule-classes nil)

  ;; rewrite rule 4
 ;; ||(x^k-x^*) - alpha_k*(Ax^k-b)|| = ||(x^k-x^*) -  alpha_k*(Ax^k-Ax^*)||
 ;;(local
 (defthm rewrite-4
   (implies (and (alist2p 'A A)
		 (alist2p 'b b)
		 (alist2p 'x^k x^k)
		 (alist2p 'x^* x^*)
		 (realp alpha-k)
		 (m-= b (m-* A x^*))   ;; by definition of x^*
		 )
	    (equal
	     (v-2norm (m-- (m-- x^k x^*) (s-* alpha-k (m-- (m-* A x^k) b))))
	     (v-2norm (m-- (m-- x^k x^*) (s-* alpha-k (m-- (m-* A x^k) (m-* A x^*)))))
	     ))
   :rule-classes nil)
 ;;)

 (defthm rewrite-4-corollary
   (implies (and (alist2p 'A A)
		 (alist2p 'b b)
		 (alist2p 'x^k x^k)
		 (alist2p 'x^k+1 x^k+1)
		 (alist2p 'x^* x^*)
		 (realp alpha-k)
		 (equal x^k+1 (m-- x^k (s-* alpha-k (f-p x^k A b))))
		 (m-= b (m-* A x^*))
		 )
	    (equal
	     (v-2norm (m-- x^k+1 x^*))
	     (v-2norm (m-- (m-- x^k x^*) (s-* alpha-k (m-- (m-* A x^k) (m-* A x^*)))))
	     ))
   :hints (("Goal"
	    :use ((:instance rewrite-3-corollary)
		  (:instance rewrite-4)
		  (:instance m-=-transitivity))
	    ))
   :rule-classes nil)

  ;; rewrite rule 5
 ;; ||(x^k-x^*) -  alpha_k*(Ax^k-Ax^*)|| = ||(x^k-x^*)-(alpha_k*Ax^k - alpha_k*Ax^*)||

 ;;(local
 (defthm rewrite-5-lemma
   (implies (and (alist2p 'A A)
		 (alist2p 'x^k x^k)
		 (alist2p 'x^* x^*)
		 (realp alpha-k)
		 )
	    (m-=
	     (s-* alpha-k (m-- (m-* A x^k) (m-* A x^*)))
	     (m-- (s-* alpha-k (m-* A x^k)) (s-* alpha-k (m-* A x^*)))
	     ))
   :hints (("Goal"
	    :use ((:instance left-s-*-distributive
	    		     (A (m-* A x^k))
	    		     (B (m-* A x^*))
	    		     (k alpha-k)))
	    ))
   :rule-classes nil)
 ;;)

 ;; ||(x^k-x^*) -  alpha_k*(Ax^k-Ax^*)|| = ||(x^k-x^*)-(alpha_k*Ax^k - alpha_k*Ax^*)||
 ;;(local
 (defthm rewrite-5
   (implies (and (alist2p 'A A)
		 (alist2p 'x^k x^k)
		 (alist2p 'x^* x^*)
		 (realp alpha-k)
		 )
	    (equal
	     (v-2norm (m-- (m-- x^k x^*) (s-* alpha-k (m-- (m-* A x^k) (m-* A x^*)))))
	     (v-2norm (m-- (m-- x^k x^*) (m-- (s-* alpha-k (m-* A x^k)) (s-* alpha-k (m-* A x^*)))))
	     ))
   :hints (("Goal"
	    :use ((:instance rewrite-5-lemma))
	    ))
   :rule-classes nil)
 ;;)

 (defthm rewrite-5-corollary
   (implies (and (alist2p 'A A)
		 (alist2p 'b b)
		 (alist2p 'x^k x^k)
		 (alist2p 'x^k+1 x^k+1)
		 (alist2p 'x^* x^*)
		 (realp alpha-k)
		 (equal x^k+1 (m-- x^k (s-* alpha-k (f-p x^k A b))))
		 (m-= b (m-* A x^*))
		 )
	    (equal
	     (v-2norm (m-- x^k+1 x^*))
	     (v-2norm (m-- (m-- x^k x^*) (m-- (s-* alpha-k (m-* A x^k)) (s-* alpha-k (m-* A x^*)))))
	     ))
   :hints (("Goal"
	    :use ((:instance rewrite-4-corollary)
		  (:instance rewrite-5)
		  (:instance m-=-transitivity))
	    ))
   :rule-classes nil)

 ;; rewrite-6-lemma
 ;; (x^k-x^*)-(alpha_k*Ax^k - alpha_k*Ax^*)  =
 ;; (x^k-x^*)-alpha_k*Ax^k + alpha_k*Ax^*
 ;;(local
 (defthm rewrite-6-lemma
   (implies (and (alist2p 'A A)
		 (alist2p 'x^k x^k)
		 (alist2p 'x^* x^*)
		 (realp alpha-k)
		 )
	    (m-=
	     (m-- (m-- x^k x^*) (m-- (s-* alpha-k (m-* A x^k)) (s-* alpha-k (m-* A x^*))))
	     (m-+ (m-- (m-- x^k x^*) (s-* alpha-k (m-* A x^k))) (s-* alpha-k (m-* A x^*)))
	     ))
   :hints (("Goal"
	    :use ((:instance +-associative-4elem-1
			     (A x^k)
			     (B x^*)
			     (C (s-* alpha-k (m-* A x^k)))
			     (D (s-* alpha-k (m-* A x^*)))))
	    ))
   :rule-classes nil)
 ;;)

  ;; ||(x^k-x^*)-(alpha_k*Ax^k - alpha_k*Ax^*)|| = ||x^k - alpha_k*Ax^k - x^* + alpha_k*Ax^*||
 ;;(local
 (defthm rewrite-6
   (implies (and (alist2p 'A A)
		 (alist2p 'x^k x^k)
		 (alist2p 'x^* x^*)
		 (realp alpha-k)
		 )
	    (equal
	     (v-2norm (m-- (m-- x^k x^*) (m-- (s-* alpha-k (m-* A x^k)) (s-* alpha-k (m-* A x^*)))))
	     (v-2norm (m-+ (m-- (m-- x^k x^*) (s-* alpha-k (m-* A x^k))) (s-* alpha-k (m-* A x^*))))
	     ))
   :hints (("Goal"
	    :use ((:instance rewrite-6-lemma))
	    ))
   :rule-classes nil)
 ;;)

 (defthm rewrite-6-corollary
   (implies (and (alist2p 'A A)
		 (alist2p 'b b)
		 (alist2p 'x^k x^k)
		 (alist2p 'x^k+1 x^k+1)
		 (alist2p 'x^* x^*)
		 (realp alpha-k)
		 (equal x^k+1 (m-- x^k (s-* alpha-k (f-p x^k A b))))
		 (m-= b (m-* A x^*))
		 )
	    (equal
	     (v-2norm (m-- x^k+1 x^*))
	     (v-2norm (m-+ (m-- (m-- x^k x^*) (s-* alpha-k (m-* A x^k))) (s-* alpha-k (m-* A x^*))))
	     ))
   :hints (("Goal"
	    :use ((:instance rewrite-5-corollary)
		  (:instance rewrite-6)
		  (:instance m-=-transitivity))
	    :in-theory '(minimal-theory)
	    ))
   :rule-classes nil)

 ;; (x^k-x^*)-(alpha_k*Ax^k - alpha_k*Ax^*) =
 ;; (x^k - alpha_k*Ax^k) - (x^* - alpha_k*Ax^*)
 ;;(local
 (defthm rewrite-7-lemma
   (implies (and (alist2p 'A A)
		 (alist2p 'x^k x^k)
		 (alist2p 'x^* x^*)
		 (realp alpha-k)
		 )
	    (m-=
	     (m-+ (m-- (m-- x^k x^*) (s-* alpha-k (m-* A x^k))) (s-* alpha-k (m-* A x^*)))
	     (m-- (m-- x^k (s-* alpha-k (m-* A x^k))) (m-- x^* (s-* alpha-k (m-* A x^*))))
	     ))
   :hints (("Goal"
	    :use ((:instance +-associative-4elem-2
			     (A x^k)
			     (B x^*)
			     (C (s-* alpha-k (m-* A x^k)))
			     (D (s-* alpha-k (m-* A x^*)))))
	    ))
   :rule-classes nil)
 ;;)
 
 ;; ||(x^k-x^*)-(alpha_k*Ax^k - alpha_k*Ax^*)|| = ||x^k - alpha_k*Ax^k - (x^* - alpha_k*Ax^*)||
 ;;(local
 (defthm rewrite-7
   (implies (and (alist2p 'A A)
		 (alist2p 'x^k x^k)
		 (alist2p 'x^* x^*)
		 (realp alpha-k)
		 )
	    (equal
	     (v-2norm (m-+ (m-- (m-- x^k x^*) (s-* alpha-k (m-* A x^k))) (s-* alpha-k (m-* A x^*))))
	     (v-2norm (m-- (m-- x^k (s-* alpha-k (m-* A x^k))) (m-- x^* (s-* alpha-k (m-* A x^*)))))
	     ))
   :hints (("Goal"
	    :use ((:instance rewrite-7-lemma))
	    ))
   :rule-classes nil)
 ;;)

 (defthm rewrite-7-corollary
   (implies (and (alist2p 'A A)
		 (alist2p 'b b)
		 (alist2p 'x^k x^k)
		 (alist2p 'x^k+1 x^k+1)
		 (alist2p 'x^* x^*)
		 (realp alpha-k)
		 (equal x^k+1 (m-- x^k (s-* alpha-k (f-p x^k A b))))
		 (m-= b (m-* A x^*))
		 )
	    (equal
	     (v-2norm (m-- x^k+1 x^*))
	     (v-2norm (m-- (m-- x^k (s-* alpha-k (m-* A x^k))) (m-- x^* (s-* alpha-k (m-* A x^*)))))
	     ))
   :hints (("Goal"
	    :use ((:instance rewrite-6-corollary)
		  (:instance rewrite-7)
		  (:instance m-=-transitivity))
	    :in-theory '(minimal-theory)
	    ))
   :rule-classes nil)

 ;; rewrite-8

 ;; alpha_k*(A*x^k) = alpha_k*Ax^k
 ;;(local
 (defthm rewrite-8-lemma1-lemma1
   (implies (and (alist2p 'A A)
 		 (alist2p 'x^k x^k)
 		 (realp alpha-k)
 		 )
 	    (m-=
 	     (s-* alpha-k (m-* A x^k))
 	     (m-* (s-* alpha-k A) x^k)
 	     ))
   :hints (("Goal"
 	    :use ((:instance s-*-associative
 			     (A A)
 			     (x x^k)
 			     (k alpha-k)))))
   :rule-classes nil)
 ;;)

  ;; x^k - alpha_k*(A*x^k) = x^k - alpha_k*Ax^k
 ;;(local
 (defthm rewrite-8-lemma1-lemma2
   (implies (and (alist2p 'A A)
 		 (alist2p 'x^k x^k)
 		 (realp alpha-k)
 		 )
 	    (m-=
 	     (m-- x^k (s-* alpha-k (m-* A x^k)))
 	     (m-- x^k (m-* (s-* alpha-k A) x^k))
 	     ))
   :hints (("Goal"
 	    :use ((:instance rewrite-8-lemma1-lemma1))))
   :rule-classes nil
   )
 ;;)

  ;; x^k - alpha_k*A*x^k = (I - alpha_k*A)x^k
 ;;(local
 (defthm rewrite-8-lemma1-lemma3
   (implies (and (alist2p 'A A)
 		 (alist2p 'x^k x^k)
 		 (realp alpha-k)
 		 )
 	    (m-=
 	     (m-- x^k (m-* (s-* alpha-k A) x^k))
 	     (m-* (m-- (m-1 (r x^k)) (s-* alpha-k A)) x^k)
 	     ))
   :hints (("Goal"
 	    :use ((:instance extract-common-vector
 			     (A (s-* alpha-k A))
 			     (b x^k)))))
   :rule-classes nil
   )
 ;;)

  ;; x^k - alpha_k*(A*x^k) = (I - alpha_k*A)x^k
 ;;(local
 (defthm rewrite-8-lemma1
   (implies (and (alist2p 'A A)
 		 (alist2p 'x^k x^k)
 		 (realp alpha-k)
 		 )
 	    (m-=
 	     (m-- x^k (s-* alpha-k (m-* A x^k)))
 	     (m-* (m-- (m-1 (r x^k)) (s-* alpha-k A)) x^k)
 	     ))
   :hints (("Goal"
 	    :use ((:instance rewrite-8-lemma1-lemma2)
		  (:instance rewrite-8-lemma1-lemma3))))
   :rule-classes nil
   )
 ;;)

  ;; x^* - alpha_k*(A*x^*) = (I - alpha_k*A)x^*
 ;;(local
 (defthm rewrite-8-lemma2
   (implies (and (alist2p 'A A)
 		 (alist2p 'x^* x^*)
 		 (realp alpha-k)
 		 )
 	    (m-=
 	     (m-- x^* (s-* alpha-k (m-* A x^*)))
 	     (m-* (m-- (m-1 (r x^*)) (s-* alpha-k A)) x^*)
 	     ))
   :hints (("Goal"
 	    :use ((:instance rewrite-8-lemma1
			     (x^k x^*)))))
   :rule-classes nil
   )
 ;;)

 ;;(local
 (defthm rewrite-8-lemma
   (implies (and (alist2p 'A A)
		 (alist2p 'x^k x^k)
 		 (alist2p 'x^* x^*)
 		 (realp alpha-k)
 		 )
 	    (m-=
 	     (m-- (m-- x^k (s-* alpha-k (m-* A x^k)))
		  (m-- x^* (s-* alpha-k (m-* A x^*))))
 	     (m-- (m-* (m-- (m-1 (r x^k)) (s-* alpha-k A)) x^k)
		  (m-* (m-- (m-1 (r x^*)) (s-* alpha-k A)) x^*))
 	     ))
   :hints (("Goal"
 	    :use ((:instance rewrite-8-lemma1)
		  (:instance rewrite-8-lemma2)
		  (:instance subtraction-congruence
			     (x1 (m-- x^k (s-* alpha-k (m-* A x^k))))
			     (x2 (m-* (m-- (m-1 (r x^k)) (s-* alpha-k A)) x^k))
			     (y1 (m-- x^* (s-* alpha-k (m-* A x^*))))
			     (y2 (m-* (m-- (m-1 (r x^*)) (s-* alpha-k A)) x^*))))
	    :in-theory '(minimal-theory)))
   :rule-classes nil
   )
 ;;)


;; ||x^k - alpha_k*Ax^k - (x^* - alpha_k*Ax^*)|| =
;; ||(I - alpha_k*A)x^k - (I - alpha_k*A)x^*|| 
(defthm rewrite-8
   (implies (and (alist2p 'A A)
		 (alist2p 'x^k x^k)
 		 (alist2p 'x^* x^*)
 		 (realp alpha-k)
 		 )
 	    (equal
 	     (v-2norm (m-- (m-- x^k (s-* alpha-k (m-* A x^k)))
			    (m-- x^* (s-* alpha-k (m-* A x^*)))))
 	     (v-2norm (m-- (m-* (m-- (m-1 (r x^k)) (s-* alpha-k A)) x^k)
			    (m-* (m-- (m-1 (r x^*)) (s-* alpha-k A)) x^*)))
 	     ))
   :hints (("Goal"
	    :do-not-induct t
 	    :use ((:instance rewrite-8-lemma))))
   :rule-classes nil
   )

 (defthm rewrite-8-corollary
   (implies (and (alist2p 'A A)
		 (alist2p 'b b)
		 (alist2p 'x^k x^k)
		 (alist2p 'x^k+1 x^k+1)
		 (alist2p 'x^* x^*)
		 (realp alpha-k)
		 (equal x^k+1 (m-- x^k (s-* alpha-k (f-p x^k A b))))
		 (m-= b (m-* A x^*))
		 )
	    (equal
	     (v-2norm (m-- x^k+1 x^*))
	     (v-2norm (m-- (m-* (m-- (m-1 (r x^k)) (s-* alpha-k A)) x^k)
			    (m-* (m-- (m-1 (r x^*)) (s-* alpha-k A)) x^*)))
	     ))
   :hints (("Goal"
	    :use ((:instance rewrite-7-corollary)
		  (:instance rewrite-8)
		  (:instance m-=-transitivity))
	    :in-theory '(minimal-theory)
	    ))
   :rule-classes nil)

;; ||I*x^k - alpha_k*Ax^k - (I*x^* - alpha_k*Ax^*)|| =
;; ||(I - alpha_k*A)x^k - (I - alpha_k*A)x^*|| 
(defthm rewrite-9-lemma
   (implies (and (alist2p 'A A)
		 (alist2p 'x^k x^k)
 		 (alist2p 'x^* x^*)
		 (equal (r x^k) (r x^*))
 		 (realp alpha-k)
 		 )
 	    (m-=
 	     (m-- (m-* (m-- (m-1 (r x^k)) (s-* alpha-k A)) x^k)
		  (m-* (m-- (m-1 (r x^*)) (s-* alpha-k A)) x^*))
 	     (m-* (m-- (m-1 (r x^k)) (s-* alpha-k A))
		  (m-- x^k x^*))
 	     ))
   :hints (("Goal"
 	    :use ((:instance m-*-distributive-over-m--
			     (X (m-- (m-1 (r x^k)) (s-* alpha-k A)))
			     (y x^k)
			     (z x^*)))
	    ))
   :rule-classes nil
   )

 (defthm rewrite-9
   (implies (and (alist2p 'A A)
		 (alist2p 'x^k x^k)
 		 (alist2p 'x^* x^*)
		 (equal (r x^k) (r x^*))
 		 (realp alpha-k)
 		 )
 	    (equal
 	     (v-2norm (m-- (m-* (m-- (m-1 (r x^k)) (s-* alpha-k A)) x^k)
			    (m-* (m-- (m-1 (r x^*)) (s-* alpha-k A)) x^*)))
 	     (v-2norm (m-* (m-- (m-1 (r x^k)) (s-* alpha-k A))
			    (m-- x^k x^*)))
 	     ))
   :hints (("Goal"
 	    :use ((:instance rewrite-9-lemma)
		  (:instance 2norm-congruence
			     (X (m-- (m-* (m-- (m-1 (r x^k)) (s-* alpha-k A)) x^k)
				     (m-* (m-- (m-1 (r x^*)) (s-* alpha-k A)) x^*)))
			     (Y (m-* (m-- (m-1 (r x^k)) (s-* alpha-k A))
				     (m-- x^k x^*)))))
	    ))
   :rule-classes nil
   )

;; final rewriting theorem
 (defthm rewrite-final
   (implies (and (alist2p 'A A)
		 (alist2p 'b b)
		 (alist2p 'x^k x^k)
		 (alist2p 'x^k+1 x^k+1)
		 (alist2p 'x^* x^*)
		 (realp alpha-k)
		 (equal x^k+1 (m-- x^k (s-* alpha-k (f-p x^k A b))))
		 (m-= b (m-* A x^*))
		 (equal (r x^k) (r x^*))
		 )
	    (equal
	     (v-2norm (m-- x^k+1 x^*))
	     (v-2norm (m-* (m-- (m-1 (r x^k)) (s-* alpha-k A))
			    (m-- x^k x^*)))
	     ))
   :hints (("Goal"
	    :use ((:instance rewrite-8-corollary)
		  (:instance rewrite-9)
		  (:instance m-=-transitivity))
	    :in-theory '(minimal-theory)
	    ))
   :rule-classes nil)

;; --------------------- matrix norm --------------------- ;;
;; proving ||(I-alpha_kA)(x^k-x^*)|| <= ||I-alpha_kA||||x^k-x^*||
;; use the definition of matrix norms
(defthm matrix-norm-def-lemma
  (implies (and (alist2p 'x x)
		(m-normp M M-Norm)
		(equal (c M) (r x))
	        (equal (c x) 1))
	   (<= (v-2norm (m-* M x))
	       (* M-Norm M-Norm (v-2norm x))))
  :hints (("Goal"
	   :use ((:instance m-normp-forall-necc))))
  )

(defthm matrix-norm-def-lemma1-lemma1
  (implies (and (alist2p 'a a)
		(alist2p 'b b)
		(equal (r a) (r b))
		(equal (c a) (c b)))
	   (alist2p 'x (m-+ a b))))

(defthm matrix-norm-def-lemma1-lemma2
  (implies (and (alist2p 'a a)
		(alist2p 'b b)
		(equal (r a) (r b))
		(equal (c a) (c b)))
	   (and (alist2p 'c (m-- b))
		(equal (r a) (r (m-- b)))
		(equal (c a) (c (m-- b))))))

(defthm matrix-norm-def-lemma1-lemma3
  (implies (and (alist2p 'a a)
		(alist2p 'b b)
		(equal (r a) (r b))
		(equal (c a) (c b)))
	   (alist2p 'x (m-+ a (m-- b))))
  :hints (("Goal"
	   :use ((:instance matrix-norm-def-lemma1-lemma1)
		 (:instance matrix-norm-def-lemma1-lemma2)))))

(defthm matrix-norm-def-lemma1-lemma4
  (implies (and (alist2p 'a a)
		(alist2p 'b b)
		(equal (r a) (r b))
		(equal (c a) (c b)))
	   (alist2p 'x (m-- a b)))
  :hints (("Goal"
	   :use ((:instance matrix-norm-def-lemma1-lemma3)))))


(defthm matrix-norm-def
  (implies (and (alist2p 'A A)
		(alist2p 'x^k x^k)
		(alist2p 'x^* x^*)
		(equal (c A) (r x^k))
		(equal (c x^k) 1)
		(equal (r x^k) (r x^*))
		(equal (c x^k) (c x^*))
		(realp alpha-k)
		(m-normp (m-- (m-1 (r x^k)) (s-* alpha-k A))
			 M-Norm)
		)
	   (<= (v-2norm (m-* (m-- (m-1 (r x^k)) (s-* alpha-k A))
			     (m-- x^k x^*)))
	       (* M-Norm M-Norm (v-2norm (m-- x^k x^*)))))
  :hints (("Goal"
	   :use ((:instance matrix-norm-def-lemma
			    (M (m-- (m-1 (r x^k)) (s-* alpha-k A)))
			    (x (m-- x^k x^*)))
		 (:instance matrix-norm-def-lemma1-lemma4
			    (a x^k)
			    (b x^*))
		 ))))

(defthm matrix-norm-corollary
  (implies (and (alist2p 'A A)
		(alist2p 'x^k x^k)
		(alist2p 'x^* x^*)
		(equal (c A) (r x^k))
		(equal (c x^k) 1)
		(equal (r x^k) (r x^*))
		(equal (c x^k) (c x^*))
		(realp alpha-k)
		(m-normp (m-- (m-1 (r x^k)) (s-* alpha-k A))
			 M-Norm)
		(alist2p 'b b)
		(alist2p 'x^k+1 x^k+1)
		(equal x^k+1 (m-- x^k (s-* alpha-k (f-p x^k A b))))
		(m-= b (m-* A x^*))
		)
	   (<= (v-2norm (m-- x^k+1 x^*))
	       (* M-Norm M-Norm (v-2norm (m-- x^k x^*)))))
  :hints (("Goal"
	   :use ((:instance rewrite-final)
		 (:instance matrix-norm-def))))
  )

;; Let's prove something even more challenging....
;; ||I-alpha_kA||||x^k-x^*|| <= max{|1-alpha_k L|,|1-alpha_k mu|}||x^k-x^*||

;; First, given mu*I \preceq A and alpha_k > 0
;; => alpha_k*mu*I \preceq alpha_k*A
;; Also, given A \preceq L*I and alpha_k > 0
;; => alpha_k*A \preceq alpha_k*L*I


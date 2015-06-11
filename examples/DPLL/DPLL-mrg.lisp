;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (13th March, 2014)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software

(in-package "ACL2")
(include-book "std/util/define" :dir :system)
(include-book "misc/eval" :dir :system) ; Define must-succeed and must-fail macros.
(include-book "tools/bstar" :dir :system) 
(include-book "ihs/ihs-init" :dir :system) ; for disable-theory and enable-theory

(deftheory before-arith (current-theory :here))
(include-book "arithmetic/top-with-meta" :dir :system)
(deftheory after-arith (current-theory :here))
(deftheory arithmetic-book-only (set-difference-theories (theory 'after-arith) (theory 'before-arith)))

;; for the clause processor to work
(include-book "../../top" :ttags :all)
(logic)
:set-state-ok t
:set-ignore-ok t
(tshell-ensure)

(local
 (progn
   (defun my-smtlink-expt-config ()
     (declare (xargs :guard t))
     (make-smtlink-config :dir-interface "../..//z3_interface"
			  :dir-files    "z3\_files"
			  :SMT-module   "RewriteExpt"
			  :SMT-class    "to_smt_w_expt"
			  :smt-cmd      "python"
			  :dir-expanded "expanded"))
   (defattach smt-cnf my-smtlink-expt-config)))


;;; some functions and bounds on parameters that we use throughout the proof
(defconst *g1-min* (/ 65536))
(defconst *g1-max* (/ 8))
(defconst *g2* (- (/ 1/3200 5)))
(defconst *Kt-min* (/ 2))
(defconst *Kt-max* (/ 9 10))
(defconst *ccode* 1)
(defconst *N* 1)  ; (mrg) I really don't like having a constant *N* and a variable n.  Need to rename one of them.
(defconst *fref* 1)
(defconst *alpha* 1)
(defconst *beta* 1)
(defconst *f0* 1)
(defconst *vcenter* 1)

(define hyp-alist (stuff)
  :guard t
  :returns (x alistp)
  :enabled t
  (cond ( (equal stuff nil) nil )
        ( (and (consp stuff) (consp (cdr stuff)))
	  (cons (cons (car stuff) (cadr stuff)) (hyp-alist (cddr stuff))) )
	( t nil)))

(define hyp-var (name stuff-a)
  :guard (and (symbolp name) (alistp stuff-a))
  :enabled t
  :returns (v rationalp)
  (b* ( (v (cdr (assoc name stuff-a)))
	((when (rationalp v)) v)
	(- (if v (er hard? 'hyp-fn "hyp-fn: ~x0 isn't rational~%" name)
		 (er hard? 'hyp-fn "hyp-fn: ~x0 needed but not provided~%" name))))
	0))


(define hyp-fn-help (stuff stuff0)
  :guard (and (alistp stuff) (alistp stuff0))
  :returns (g atom)
  :enabled t
  (if (endp stuff) t
      (let ((name (caar stuff)) (var (cdar stuff)) (tail (cdr stuff)))
           (and (cond ((equal name :g1) (and (rationalp var) (< *g1-min* var) (< var *g1-max*)))
	              ((equal name :Kt) (and (rationalp var) (< *Kt-min* var) (< var *Kt-max*)))
	              ((equal name :v0) (and (rationalp var) (< 0 var)))
	              ((equal name :dv)
		       (b* ( (g1 (hyp-var :g1 stuff0))
		             (dv-bound (/ (* *alpha* g1) (* 4 *beta* )))
		             (dv var) )
			   (and (rationalp dv) (< (- dv-bound) dv) (< dv dv-bound))))
		      (t (b* ((- (er hard? 'hyp-fn "hyp-fn: unknown key -- ~x0~%" name))) t)))
                (hyp-fn-help tail stuff0)))))

(define hyp-fn (stuff)
  :guard t
  :returns (g atom)
  :enabled t
  (let ( (stuff-a (hyp-alist stuff)) )
  	 (hyp-fn-help stuff-a stuff-a) ))

;  I'll provide a macro version for all constraints because Smtlink
;  can't expand general functions (e.g. hyp-fn and it's family).
(defmacro hyp-macro (g1 Kt v0 dv)
  `(and (rationalp ,g1) (< *g1-min* ,g1) (< ,g1 *g1-max*)
        (rationalp ,Kt) (< *Kt-min* ,Kt) (< ,Kt *Kt-max*)
        (rationalp ,v0) (< 0 ,v0)
        (rationalp ,dv) (< (- (* (/ 4) (/ *alpha* *beta*) ,g1)) ,dv)
		        (< ,dv (* (/ 4) (/ *alpha* *beta*) ,g1))))


;; A few checks to get a warm fuzzy feeling that hyp-fn probably does what we intended
(cw "hyp-fn: test 1~%")
(must-succeed (thm (equal (hyp-fn (list :g1 g1))
	                  (and (rationalp g1) (< *g1-min* g1) (< g1 *g1-max*)))))
(cw "hyp-fn: test 2~%")
(must-succeed (thm (equal (hyp-fn (list :g1 x))
	                  (and (rationalp x) (< *g1-min* x) (< x *g1-max*)))))
(cw "hyp-fn: test 3~%")
(must-succeed (thm (equal (hyp-fn (list :Kt Kt))
                          (and (rationalp Kt) (< *Kt-min* Kt) (< Kt *Kt-max*)))))
(cw "hyp-fn: test 4~%")
(must-succeed (thm (equal (hyp-fn (list :v0 v0))
                          (and (rationalp v0) (< 0 v0)))))
(cw "hyp-fn: test 5~%")
(must-succeed (thm (equal (hyp-fn (list :dv dv :g1 g1))
	                  (and (rationalp g1) (< *g1-min* g1) (< g1 *g1-max*)
	                       (rationalp dv) (< (- (* (/ 4) (/ *alpha* *beta*) g1)) dv)
	                                      (< dv (* (/ 4) (/ *alpha* *beta*) g1))))))
(cw "hyp-fn: test 6~%")
(must-succeed (thm (equal (hyp-fn (list :g1 g1 :Kt Kt :v0 v0 :dv dv))
	                  (hyp-macro g1 Kt v0 dv))))
(cw "hyp-fn: test 7~%")
(must-succeed (thm (implies (hyp-fn (list :g1 g1 :Kt Kt :v0 v0 :dv dv))
			    (< (* 4 *beta* dv) (* *alpha* *g1-max*)))))
(cw "hyp-fn: test 8~%")
(must-fail (thm (implies (hyp-fn (list :g1 g1 :Kt Kt :v0 v0 :dv dv))
			 (< (* 5 *beta* dv) (* *alpha* *g1-max*)))))
; (must-fail (thm (implies (hyp-fn (list :gx g1)) t)))
;   The er in hyp-fn logically returns null, and no error is reported when used in a proof.
;   I should change hyp-fn to return t if any undefined variable is requested.



(define mu ()
  :returns (f rationalp)
  (/ *f0* (* *N* *fref*)))

(define fdco (n v0 dv g1)
  :guard (and (rationalp n) (hyp-fn (list :v0 v0 :dv dv :g1 g1)) (< -1 (* *beta* n g1)))
  :returns (f rationalp :hyp :guard)
  (/ (* (mu) (+ 1 (* *alpha* (+ v0 dv)))) (+ 1 (* *beta* n g1))))
 
(define equ-c (v0)
  :guard (hyp-fn (list :v0 v0))
  :returns (c rationalp :hyp :guard)
  (- (* *f0* (+ 1 (* *alpha* v0)) (/ (* *beta* *N* *fref*))) (/ *beta*)))

(defthm fdco-and-equ-c
  (implies (and (hyp-fn (list :v0 v0 :g1 g1)) (equal (* n g1) (equ-c v0)))
  	   (equal (fdco n v0 0 g1) 1))
  :hints(("Goal" :in-theory (enable fdco equ-c mu))))

(define gamma (Kt)
  :guard (hyp-fn (list :Kt Kt))
  :returns (g rationalp :hyp :guard)
  (- 1 Kt)
  ///
  (more-returns (g (and (< 0 g) (< g 1) (not (equal g 0))) :hyp :guard :name gamma-bounds)))

(define m (n v0 g1)
  :guard (and (integerp n) (hyp-fn (list :v0 v0 :g1 g1)))
  :returns (mm rationalp :hyp :guard)
  (- (/ (equ-c v0) g1) n))

(define dv0 ()
  :returns (_dv0 rationalp)
  (* -2 *g2*))

;;:start-proof-tree

(define h-ok (h g1 v0)
  :guard (rational-listp (list g1 v0))
  :returns (ok atom)
  :enabled t
  (and (integerp h) (< 0 (+ (* h g1) (* *f0* (+ 1 (* *alpha* v0)) (/ (* *beta* *N* *fref*)))))))

(define h-list-ok (h-list g1 v0)
  :guard (and (integer-listp h-list) (rational-listp (list g1 v0)))
  :returns (ok atom)
  :enabled t
  (if (endp h-list) t
      (and (h-ok (car h-list) g1 v0) (h-list-ok (cdr h-list) g1 v0))))

(define B-term-expt (Kt h)
  :guard (and (integerp h) (hyp-fn (list :Kt Kt)))
  :returns (x rationalp :hyp :guard)
  (expt (gamma Kt) (- h)))

(encapsulate ()
  (local (in-theory (enable equ-c mu))) ; needed todischarge guard conjecture for B-term-rest
  (define B-term-rest (h v0 dv g1)
    :guard (and (integerp h) (hyp-fn (list :v0 v0 :dv dv :g1 g1)) (h-ok h g1 v0))
    :returns (x rationalp :hyp :guard)
    (- (* (mu) (/ (+ 1 (* *alpha* (+ v0 dv))) (+ 1 (* *beta* (+ (* h g1) (equ-c v0)))))) 1)))

(define B-term (h v0 dv g1 Kt)
  :guard (and (integerp h) (hyp-fn (list :v0 v0 :dv dv :g1 g1 :Kt Kt)) (h-ok h g1 v0))
  :returns (x rationalp :hyp :guard)
  (* (B-term-expt Kt h) (B-term-rest h v0 dv g1)))

(encapsulate()
  (local (defthm lemma-1  ; needed for the guard conjecture of B_sum.
    (implies (and (< 0 (+ 1 v0 (* g1 h_lo)))
    	       (integerp h_lo) (integerp h_hi)
	       (rationalp v0)
	       (< 0 v0)
	       (rationalp g1)
	       (< 1 (* 65536 g1))
	       (<= h_lo h_hi))
	     (< 0 (+ 1 v0 (* g1 h_hi))))
    :hints(("Goal" :nonlinearp t))))

  (define B_sum (h_lo h_hi v0 dv g1 Kt)
    :guard (and (integerp h_lo) (integerp h_hi) (<= 0 h_lo) (<= h_lo (1+ h_hi))
		(hyp-fn (list :v0 v0 :dv dv :g1 g1 :Kt Kt))
		(h-list-ok (list h_lo (- h_hi)) g1 v0))
    :returns (x rationalp :hyp :guard)
    :measure (if (and (integerp h_hi) (integerp h_lo) (>= h_hi h_lo))
		 (1+ (- h_hi h_lo))
		 0)
    (if (and (integerp h_hi) (integerp h_lo) (>= h_hi h_lo))
	(+ (B-term h_hi v0 dv g1 Kt ) (B-term (- h_hi) v0 dv g1 Kt)
	   (B_sum h_lo (- h_hi 1) v0 dv g1 Kt))
	0)))


(encapsulate ()
  ; disable arithmetic5 or ACL2 gets lost when trying to prove rationalp-of-B-expt
  (local (disable-theory (theory 'arithmetic-book-only)))

  (local (defthm B-expt-lemma  ; needed for rationalp-of-B-expt
    (implies (and (rationalp x) (< 0 x) (integerp n))
    	     (let ((y (expt x n))) (and (< 0 y) (rationalp y))))))

  (define B-expt (Kt n)
    :guard (and (integerp n) (hyp-fn (list :Kt Kt)))
    :returns (x rationalp :hyp :guard)
    (expt (gamma Kt) (- n 2))
    ///
    (more-returns (x (< 0 x) :hyp :guard :name B-expt->-0))))

(define B (n v0 dv g1 Kt)
  :guard (and (integerp n) (<= 2 n) (hyp-fn (list :v0 v0 :dv dv :g1 g1 :Kt Kt))
              (h-list-ok (list 1 (- 2 n)) g1 v0))
  :returns (x rationalp :hyp :guard)
  (* (B-expt Kt n)
     (B_sum 1 (- n 2) v0 dv g1 Kt)))

(define smt-std-hint (clause-name)
  :guard (stringp clause-name)
  `( (:expand ((:functions ( (A rationalp)
                             (B-term rationalp)
			     (B-term-expt rationalp)
			     (B-term-rest rationalp)
			     (dv0 rationalp)
			     (delta rationalp)
			     (delta-3 rationalp)
			     (equ-c rationalp)
			     (fdco rationalp)
			     (gamma rationalp)
			     (m rationalp)
			     (mu rationalp)
			     (phi-2n-1 rationalp)))
	       (:expansion-level 1)))
     (:uninterpreted-functions ((expt rationalp rationalp rationalp)))
     (:python-file ,clause-name)))

(defthm B-term-neg
  (implies (and (integerp h) (<= 1 h) (< h (/ (* 2 g1)))
  		(hyp-macro g1 Kt v0 dv))
	   (< (+ (B-term h v0 dv g1 Kt) (B-term (- h) v0 dv g1 Kt)) 0))
    :hints (("Goal"
      :in-theory (enable B-term B-term-expt B-term-rest mu equ-c gamma dv0)
      :clause-processor
      (smtlink-custom-config clause (smt-std-hint "B-term-neg") state)))
    :rule-classes :linear)

; B-sum-neg: show that the sum of a bunch of B-term pairs is negative.
;   This is a trivial induction proof that the sum of a bunch of negative values is negative.
;   We need B-term-neg to know that the terms in the sum are individually negative.
; B-term-neg gets a 'non-rec' warning.  I suspect that's why I need to disable it and
;   then specify a particular instance in the proof for B-sum-neg below.
;   On the other hand, I wonder if we could get a "computed hint" or similar to recognize
;   when the smtlink clause processor is applicable, and use it automatically.
;   In that case, we might not need to explicitly state and prove B-term-neg.
(defthm B-sum-neg
  (implies (and (integerp n-minus-2) (<= 1 n-minus-2) (< n-minus-2 (/ (* 2 g1)))
  		(hyp-fn (list :v0 v0 :dv dv :g1 g1 :Kt Kt)))
	   (< (B_sum 1 n-minus-2 v0 dv g1 Kt) 0))
  :hints (("Goal" :in-theory (e/d (B_sum) (B-term)))))

(defthm B-neg
  (implies (and (integerp n) (<= 3 n) (< n (/ (* 2 g1)))
  		(hyp-macro g1 Kt v0 dv))
           (< (B n v0 dv g1 Kt) 0))
  :hints (("Goal" :in-theory (enable B gamma B-expt)
    :clause-processor
    (smtlink-custom-config clause
      '( (:expand ((:functions ((B rationalp) (B-expt rationalp) (gamma rationalp)))
		   (:expansion-level 1)))
         (:uninterpreted-functions (
	   (expt rationalp integerp rationalp)
	   (B_sum integerp integerp rationalp rationalp rationalp rationalp  rationalp)))
         (:python-file "B-neg") ;;mktemp
	 (:hypothesize ((< (B_sum 1 (+ -2 n) v0 dv g1 kt) 0)))
	 (:use ((:hypo ((B-sum-neg)))))) state))))


(defun A (nn phi0 v0 dv g1 Kt)
  (+ (* (expt (gamma Kt) (- (* 2 nn) 1)) phi0)
     (* (expt (gamma Kt) (- (* 2 nn) 2))
	(- (fdco (m nn v0 g1) v0 dv g1) 1))
     (* (expt (gamma Kt) (- (* 2 nn) 3))
	(- (fdco (1+ (m nn v0 g1)) v0 dv g1) 1))))

(defun phi-2n-1 (n phi0 v0 dv g1 Kt)
  (+ (A n phi0 v0 dv g1 Kt) (B n v0 dv g1 Kt)))

(defun delta (n v0 dv g1 Kt)
  (+ (- (* (expt (gamma Kt) (* 2 n))
	   (- (fdco (1- (m n v0 g1)) v0 dv g1) 1))
	(* (expt (gamma Kt) (* 2 n)) 
	   (- (fdco (m n v0 g1) v0 dv g1) 1)))
     (- (* (expt (gamma Kt) (- (* 2 n) 1))
	   (- (fdco (m n v0 g1) v0 dv g1) 1))
	(* (expt (gamma Kt) (- (* 2 n) 1))
	   (- (fdco (1+ (m n v0 g1)) v0 dv g1) 1)))
     (* (expt (gamma Kt) (1- n))
	(+ (* (expt (gamma Kt) (1+ (- n)))
	      (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
		    (1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0)))))
		 1))
	   (* (expt (gamma Kt) (1- n))
	      (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
		    (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0)))))
		 1))))))


(defun delta-3 (n v0 dv g1 Kt)
  (* (expt (gamma Kt) (+ -1 n -1 n))
     (+ (* (expt (gamma Kt) 2)
	   (- (fdco (1- (m n v0 g1)) v0 dv g1)
	      (fdco (m n v0 g1) v0 dv g1)))
	(* (expt (gamma Kt) 1)
	   (- (fdco (m n v0 g1) v0 dv g1)
	      (fdco (1+ (m n v0 g1)) v0 dv g1)))
	(* (expt (gamma Kt) (- 2 (* 2 n)))
	   (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
		 (1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0))))) 1))
	(- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
	      (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1))))


(encapsulate ()
  (local (disable-theory (theory 'arithmetic-book-only)))
  (defthm delta-rewrite-5
    (implies (and (and (integerp n) (rationalp v0) (rationalp dv) (rationalp g1) (rationalp Kt))
		  (<= 3 n) (< n (/ (* 2 g1)))
		  (< 0 v0)
		  (< 0 dv) (< dv (* (/ 4) (/ *alpha* *beta*) g1))
		  (< *g1-min* g1) (< g1 *g1-max*)
		  (< *Kt-min* Kt) (< Kt *Kt-max*))
	     (equal (delta n v0 dv g1 Kt) (delta-3 n v0 dv g1 Kt)))
    :hints (("Goal" :in-theory (enable delta delta-3 equ-c fdco mu gamma m A phi-2n-1)
		    :clause-processor
		      (smtlink-custom-config clause (smt-std-hint "B-term-neg") state)))))

(defthm stop-here nil)

;(defun delta-3-inside (n v0 dv g1)
;  (+ (* (expt (gamma) 2)
;	   (- (fdco (1- (m n v0 g1)) v0 dv g1)
;	      (fdco (m n v0 g1) v0 dv g1)))
;	(* (expt (gamma) 1)
;	   (- (fdco (m n v0 g1) v0 dv g1)
;	      (fdco (1+ (m n v0 g1)) v0 dv g1)))
;	(* (expt (gamma) (- 2 (* 2 n)))
;	   (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
;		 (1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0))))) 1))
;	(- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
;	      (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1)))
;
;(defun delta-3-inside-transform (n v0 dv g1)
;  (/ 
;   (+ (* (expt (gamma) 2)
;	 (- (fdco (1- (m n v0 g1)) v0 dv g1)
;	    (fdco (m n v0 g1) v0 dv g1)))
;      (* (expt (gamma) 1)
;	 (- (fdco (m n v0 g1) v0 dv g1)
;	    (fdco (1+ (m n v0 g1)) v0 dv g1)))
;      (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
;	    (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1))
;   (- 1
;      (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
;	 (1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0))))))))

(encapsulate ()

(local
(defthm delta-<-0-lemma1-lemma
  (implies (basic-params n 3 v0 dv g1)
	   (implies (< (+ (* (expt (gamma) 2)
			     (- (fdco (1- (m n v0 g1)) v0 dv g1)
				(fdco (m n v0 g1) v0 dv g1)))
			  (* (expt (gamma) 1)
			     (- (fdco (m n v0 g1) v0 dv g1)
				(fdco (1+ (m n v0 g1)) v0 dv g1)))
			  (* (expt (gamma) (- 2 (* 2 n)))
			     (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				   (1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0))))) 1))
			  (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				(1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1))
		       0)
		    (< (* (expt (gamma) (+ -1 n -1 n))
			  (+ (* (expt (gamma) 2)
				(- (fdco (1- (m n v0 g1)) v0 dv g1)
				   (fdco (m n v0 g1) v0 dv g1)))
			     (* (expt (gamma) 1)
				(- (fdco (m n v0 g1) v0 dv g1)
				   (fdco (1+ (m n v0 g1)) v0 dv g1)))
			     (* (expt (gamma) (- 2 (* 2 n)))
				(- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				      (1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0))))) 1))
			     (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				   (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1)))
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
				(- (fdco (1- (m n v0 g1)) v0 dv g1)
				   (fdco (m n v0 g1) v0 dv g1)))
			     (* (expt (gamma) 1)
				(- (fdco (m n v0 g1) v0 dv g1)
				   (fdco (1+ (m n v0 g1)) v0 dv g1)))
			     (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				   (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1))
			  (- 1
			     (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				(1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0)))))))
		       (expt (gamma) (- 2 (* 2 n))))
		    (< (+ (* (expt (gamma) 2)
			     (- (fdco (1- (m n v0 g1)) v0 dv g1)
				(fdco (m n v0 g1) v0 dv g1)))
			  (* (expt (gamma) 1)
			     (- (fdco (m n v0 g1) v0 dv g1)
				(fdco (1+ (m n v0 g1)) v0 dv g1)))
			  (* (expt (gamma) (- 2 (* 2 n)))
			     (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				   (1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0))))) 1))
			  (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				(1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1))
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
  (implies (and (integerp k)
		(>= k 6))
	   (< k (expt (/ (gamma)) (- k 2)))))
)

(local
 (defthm delta-<-0-lemma3-lemma2-stupidlemma
   (implies (basic-params n 3)
	    (>= n 3))))

(local
 (defthm delta-<-0-lemma3-lemma2-stupidlemma-omg
   (implies (and (rationalp a) (rationalp b) (>= a b))
	    (>= (* 2 a) (* 2 b)))))

(local
 (defthm delta-<-0-lemma3-lemma2-lemma1
   (implies (basic-params n 3)
	    (>= (* 2 n) 6))
   :hints (("Goal"
	    :use ((:instance delta-<-0-lemma3-lemma2-stupidlemma)
		  (:instance delta-<-0-lemma3-lemma2-stupidlemma-omg
			     (a n)
			     (b 3))
		  ))))
 )

(local
(defthm delta-<-0-lemma3-lemma2
  (implies (basic-params n 3)
	   (< (* 2 n)
	      (expt (/ (gamma)) (- (* 2 n) 2))))
  :hints (("Goal"
	   :use ((:instance delta-<-0-lemma3-lemma1
			   (k (* 2 n)))
		 (:instance delta-<-0-lemma3-lemma2-lemma1))))
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
				(- (fdco (1- (m n v0 g1)) v0 dv g1)
				   (fdco (m n v0 g1) v0 dv g1)))
			     (* (expt (gamma) 1)
				(- (fdco (m n v0 g1) v0 dv g1)
				   (fdco (1+ (m n v0 g1)) v0 dv g1)))
			     (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				   (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1))
			  (- 1
			     (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				(1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0)))))))
		       (* 2 n))
		    (< (/ (+ (* (expt (gamma) 2)
				(- (fdco (1- (m n v0 g1)) v0 dv g1)
				   (fdco (m n v0 g1) v0 dv g1)))
			     (* (expt (gamma) 1)
				(- (fdco (m n v0 g1) v0 dv g1)
				   (fdco (1+ (m n v0 g1)) v0 dv g1)))
			     (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				   (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1))
			  (- 1
			     (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				(1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0)))))))
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
		       (- (fdco (1- (m n v0 g1)) v0 dv g1)
			  (fdco (m n v0 g1) v0 dv g1)))
		    (* (expt (gamma) 1)
		       (- (fdco (m n v0 g1) v0 dv g1)
			  (fdco (1+ (m n v0 g1)) v0 dv g1)))
		    (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
			  (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1))
		 (- 1
		    (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
		       (1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0)))))))
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
				  (:hypothesize ((equal expt_gamma_1 1/5)
						 (equal expt_gamma_2 1/25)))))
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
  (implies (basic-params n 3 v0 dv g1 phi0)
	   (equal (A (+ n 1) phi0 v0 dv g1)
		  (+ (* (expt (gamma) (+ (* 2 n) 1)) phi0)
		     (* (expt (gamma) (* 2 n))
			(- (fdco (1- (m n v0 g1)) v0 dv g1) 1))
		     (* (expt (gamma) (- (* 2 n) 1))
			(- (fdco (m n v0 g1) v0 dv g1) 1))))))
)

(local
(defthm split-phi-2n+1-lemma1-lemma2
  (implies (basic-params n 3 v0 dv g1 phi0)
	   (equal (+ (* (expt (gamma) (+ (* 2 n) 1)) phi0)
		     (* (expt (gamma) (* 2 n))
			(- (fdco (1- (m n v0 g1)) v0 dv g1) 1))
		     (* (expt (gamma) (- (* 2 n) 1))
			(- (fdco (m n v0 g1) v0 dv g1) 1)))
		  (+ (* (+ (* (expt (gamma) (- (* 2 n) 1)) phi0)
			   (* (expt (gamma) (- (* 2 n) 2))
			      (- (fdco (m n v0 g1) v0 dv g1) 1))
			   (* (expt (gamma) (- (* 2 n) 3))
			      (- (fdco (1+ (m n v0 g1)) v0 dv g1) 1)))
			(expt (gamma) 2))
		     (- (* (expt (gamma) (* 2 n))
			   (- (fdco (1- (m n v0 g1)) v0 dv g1) 1))
			(* (expt (gamma) (* 2 n))
			   (- (fdco (m n v0 g1) v0 dv g1) 1)))
		     (- (* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (m n v0 g1) v0 dv g1) 1))
			(* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (1+ (m n v0 g1)) v0 dv g1) 1))))))
  )
)

(local
(defthm split-phi-2n+1-lemma1-A
  (implies (basic-params n 3 v0 dv g1 phi0)
	   (equal (A (+ n 1) phi0 v0 dv g1)
		  (+ (* (A n phi0 v0 dv g1) (gamma) (gamma))
		     (- (* (expt (gamma) (* 2 n))
			   (- (fdco (1- (m n v0 g1)) v0 dv g1) 1))
			(* (expt (gamma) (* 2 n))
			   (- (fdco (m n v0 g1) v0 dv g1) 1)))
		     (- (* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (m n v0 g1) v0 dv g1) 1))
			(* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (1+ (m n v0 g1)) v0 dv g1) 1)))))))
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
			   (- (fdco (1- (m n v0 g1)) v0 dv g1) 1))
			(* (expt (gamma) (* 2 n))
			   (- (fdco (m n v0 g1) v0 dv g1) 1)))
		     (- (* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (m n v0 g1) v0 dv g1) 1))
			(* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (1+ (m n v0 g1)) v0 dv g1) 1)))
		     (* (expt (gamma) (- n 1))
			(+ (* (expt (gamma) (- (- n 1)))
			      (B-term-rest (- n 1) v0 dv g1))
			   (* (expt (gamma) (- n 1))
			      (B-term-rest (- (- n 1)) v0 dv g1)))))
		  (+ (- (* (expt (gamma) (* 2 n))
			   (- (fdco (1- (m n v0 g1)) v0 dv g1) 1))
			(* (expt (gamma) (* 2 n))
			   (- (fdco (m n v0 g1) v0 dv g1) 1)))
		     (- (* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (m n v0 g1) v0 dv g1) 1))
			(* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (1+ (m n v0 g1)) v0 dv g1) 1)))
		     (* (expt (gamma) (1- n))
			(+ (* (expt (gamma) (1+ (- n)))
			      (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				    (1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0))))) 1))
			   (* (expt (gamma) (1- n))
			      (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				    (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1))))))))
)

(local
(defthm split-phi-2n+1-lemma3-delta
  (implies (basic-params n 3 v0 dv g1)
	   (equal (+ (- (* (expt (gamma) (* 2 n))
			   (- (fdco (1- (m n v0 g1)) v0 dv g1) 1))
			(* (expt (gamma) (* 2 n))
			   (- (fdco (m n v0 g1) v0 dv g1) 1)))
		     (- (* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (m n v0 g1) v0 dv g1) 1))
			(* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (1+ (m n v0 g1)) v0 dv g1) 1)))
		     (* (expt (gamma) (- n 1))
			(+ (* (expt (gamma) (- (- n 1)))
			      (B-term-rest (- n 1) v0 dv g1))
			   (* (expt (gamma) (- n 1))
			      (B-term-rest (- (- n 1)) v0 dv g1)))))
		  (delta n v0 dv g1)))
  :hints (("Goal"
	   :use ((:instance split-phi-2n+1-lemma3-delta-stupidlemma)
		 (:instance delta)))))
)

(local
(defthm split-phi-2n+1-lemma4
  (implies (basic-params n 3 v0 dv g1 phi0)
	   (equal (phi-2n-1 (1+ n) phi0 v0 dv g1)
		  (+ (A (+ n 1) phi0 v0 dv g1)
		     (B (+ n 1) v0 dv g1)))))
)

(local
(defthm split-phi-2n+1-lemma5
  (implies (basic-params n 3 v0 dv g1 phi0)
	   (equal (phi-2n-1 (1+ n) phi0 v0 dv g1)
		  (+ (+ (* (A n phi0 v0 dv g1) (gamma) (gamma))
			(- (* (expt (gamma) (* 2 n))
			      (- (fdco (1- (m n v0 g1)) v0 dv g1) 1))
			   (* (expt (gamma) (* 2 n))
			      (- (fdco (m n v0 g1) v0 dv g1) 1)))
			(- (* (expt (gamma) (- (* 2 n) 1))
			      (- (fdco (m n v0 g1) v0 dv g1) 1))
			   (* (expt (gamma) (- (* 2 n) 1))
			      (- (fdco (1+ (m n v0 g1)) v0 dv g1) 1))))
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
  (implies (basic-params n 3 v0 dv g1 phi0)
	   (equal (phi-2n-1 (1+ n) phi0 v0 dv g1)
		  (+ (* (A n phi0 v0 dv g1) (gamma) (gamma))
		     (* (gamma) (B n v0 dv g1))
		     (+ (- (* (expt (gamma) (* 2 n))
			      (- (fdco (1- (m n v0 g1)) v0 dv g1) 1))
			   (* (expt (gamma) (* 2 n))
			      (- (fdco (m n v0 g1) v0 dv g1) 1)))
			(- (* (expt (gamma) (- (* 2 n) 1))
			      (- (fdco (m n v0 g1) v0 dv g1) 1))
			   (* (expt (gamma) (- (* 2 n) 1))
			      (- (fdco (1+ (m n v0 g1)) v0 dv g1) 1)))
			(* (expt (gamma) (- n 1))
			   (+ (* (expt (gamma) (- (- n 1)))
				 (B-term-rest (- n 1) v0 dv g1))
			      (* (expt (gamma) (- n 1))
				 (B-term-rest (- (- n 1)) v0 dv g1)))))))))
)

(defthm split-phi-2n+1
  (implies (basic-params n 3 v0 dv g1 phi0)
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
  (implies (basic-params n 3 v0 dv g1 phi0 (< (phi-2n-1 n phi0 v0 dv g1) 0))
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
	     
(defthm phi-2n+1-<-0-inductive
  (implies (basic-params n 3 v0 dv g1 phi0 (< (phi-2n-1 n phi0 v0 dv g1) 0))
	   (< (phi-2n-1 (1+ n) phi0 v0 dv g1) 0))
  :hints (("Goal"
 	   :use ((:instance split-phi-2n+1)
		 (:instance delta-<-0)
		 (:instance except-for-delta-<-0)))))

(defthm phi-2n+1-<-0-inductive-corollary
  (implies (basic-params (- i 1) 3 v0 dv g1 phi0
			 (< (phi-2n-1 (- i 1) phi0 v0 dv g1) 0))
	   (< (phi-2n-1 i phi0 v0 dv g1) 0))
  :hints (("Goal"
	   :use ((:instance phi-2n+1-<-0-inductive
			    (n (- i 1)))))))

(defthm phi-2n+1-<-0-inductive-corollary-2
  (implies (basic-params (- i 1) 3 v0 dv g1 phi0
			 (< (phi-2n-1 (- i 1) phi0 v0 dv g1) 0))
	   (< (+ (A i phi0 v0 dv g1)
		 (* (B-expt i)
		    (B-sum 1 (- i 2) v0 dv g1))) 0))
  :hints (("Goal"
	   :use ((:instance phi-2n+1-<-0-inductive-corollary)))))

(defthm phi-2n+1-<-0-base
    (implies (basic-params-equal n 2 v0 dv g1 phi0)
	   (< (phi-2n-1 (1+ n) phi0 v0 dv g1) 0))
  :hints (("Goal''"
	   :clause-processor
  	   (my-clause-processor clause
  				'( (:expand ((:function ())
  					     (:expansion-level 1)))
  				  (:python-file "phi-2n+1-smaller-than-0-base")
  				  (:let ())
  				  (:hypothesize ())))))
  )

(defthm phi-2n+1-<-0-base-new
    (implies (basic-params-equal (- i 2) 1 v0 dv g1 phi0)
	   (< (phi-2n-1 (- i 1) phi0 v0 dv g1) 0))
  :hints (("Goal''"
	   :clause-processor
  	   (my-clause-processor clause
  				'( (:expand ((:function ())
  					     (:expansion-level 1)))
  				  (:python-file "phi-2n+1-smaller-than-0-base-new")
  				  (:let ())
  				  (:hypothesize ())))))
  )

(defthm phi-2n+1-<-0-base-corollary
  (implies (basic-params-equal (1- i) 2 v0 dv g1 phi0)
	   (< (phi-2n-1 i phi0 v0 dv g1) 0))
  :hints (("Goal"
	   :use ((:instance phi-2n+1-<-0-base
			    (n (- i 1))))))
  )

(defthm phi-2n+1-<-0-base-corollary-2
  (implies (basic-params-equal (1- i) 2 v0 dv g1 phi0)
	   (< (+ (A i phi0 v0 dv g1)
		 (* (B-expt i)
		    (B-sum 1 (- i 2) v0 dv g1))) 0))
  :hints (("Goal"
	   :use ((:instance phi-2n+1-<-0-base-corollary))))
  )

(defthm stupid-proof
  (implies (and (equal a f)
		(equal a i)
		(implies (and m l) l)
		(implies l (and c h))
		(implies (and c h) (and c j))
	        (implies (and a b c d) e)
		(implies (and f b c d) g)
		(implies (and f b h d e) g)
		i
		m
		(implies (and a b j d) e)
		f
		b
		l
		d)
	   g)
  :rule-classes nil)

(defthm phi-2n+1-<-0-lemma-lemma1
  (implies
 (and
     (implies
          (and (and (integerp (+ -2 i))
                    (rationalp g1)
                    (rationalp v0)
                    (rationalp phi0)
                    (rationalp dv))
               (equal (+ -2 i) 1)
               (equal g1 1/3200)
               (<= 9/10 v0)
               (<= v0 11/10)
               (<= -1/8000 dv)
               (<= dv 1/8000)
               (<= 0 phi0)
               (< phi0
                  (+ -1
                     (* (fix (+ 1 (fix (+ v0 dv))))
                        (/ (+ 1
                              (fix (* (+ 1
                                         (* (+ (fix (* (+ 1 (fix v0)) 1)) -1)
                                            (/ g1))
                                         -640)
                                      g1))))))))
          (< (phi-2n-1 (+ -1 i) phi0 v0 dv g1) 0))
     (implies
          (and (and (integerp (+ -1 i))
                    (rationalp g1)
                    (rationalp v0)
                    (rationalp phi0)
                    (rationalp dv))
               (equal (+ -1 i) 2)
               (equal g1 1/3200)
               (<= 9/10 v0)
               (<= v0 11/10)
               (<= -1/8000 dv)
               (<= dv 1/8000)
               (<= 0 phi0)
               (< phi0
                  (+ -1
                     (* (fix (+ 1 (fix (+ v0 dv))))
                        (/ (+ 1
                              (fix (* (+ 1
                                         (* (+ (fix (* (+ 1 (fix v0)) 1)) -1)
                                            (/ g1))
                                         -640)
                                      g1))))))))
          (< (+ (a i phi0 v0 dv g1)
                (* (/ (expt 5 (+ -2 i)))
                   (b-sum 1 (+ -2 i) v0 dv g1)))
             0))
     (implies
          (and (and (integerp (+ -1 i))
                    (rationalp g1)
                    (rationalp v0)
                    (rationalp dv)
                    (rationalp phi0))
               (<= 3 (+ -1 i))
               (<= (+ -1 i) 640)
               (equal g1 1/3200)
               (<= 9/10 v0)
               (<= v0 11/10)
               (<= -1/8000 dv)
               (<= dv 1/8000)
               (<= 0 phi0)
               (< phi0
                  (+ -1
                     (* (fix (+ 1 (fix (+ v0 dv))))
                        (/ (+ 1
                              (fix (* (+ 1
                                         (* (+ (fix (* (+ 1 (fix v0)) 1)) -1)
                                            (/ g1))
                                         -640)
                                      g1)))))))
               (< (phi-2n-1 (+ -1 i) phi0 v0 dv g1) 0))
          (< (+ (a i phi0 v0 dv g1)
                (* (/ (expt 5 (+ -2 i)))
                   (b-sum 1 (+ -2 i) v0 dv g1)))
             0))
     (not (or (not (integerp i)) (< i 1)))
     (implies
          (and (and (integerp (+ -1 -1 i))
                    (rationalp g1)
                    (rationalp v0)
                    (rationalp dv)
                    (rationalp phi0))
               (<= 2 (+ -1 -1 i))
               (<= (+ -1 -1 i) 640)
               (equal g1 1/3200)
               (<= 9/10 v0)
               (<= v0 11/10)
               (<= -1/8000 dv)
               (<= dv 1/8000)
               (<= 0 phi0)
               (< phi0
                  (+ -1
                     (* (fix (+ 1 (fix (+ v0 dv))))
                        (/ (+ 1
                              (fix (* (+ 1
                                         (* (+ (fix (* (+ 1 (fix v0)) 1)) -1)
                                            (/ g1))
                                         -640)
                                      g1))))))))
          (< (+ (a (+ -1 i) phi0 v0 dv g1)
                (* (/ (expt 5 (+ -2 -1 i)))
                   (b-sum 1 (+ -2 -1 i) v0 dv g1)))
             0))
     (integerp (+ -1 i))
     (rationalp g1)
     (rationalp v0)
     (rationalp dv)
     (rationalp phi0)
     (<= 2 (+ -1 i))
     (<= (+ -1 i) 640)
     (equal g1 1/3200)
     (<= 9/10 v0)
     (<= v0 11/10)
     (<= -1/8000 dv)
     (<= dv 1/8000)
     (<= 0 phi0)
     (< phi0
        (+ -1
           (* (fix (+ 1 (fix (+ v0 dv))))
              (/ (+ 1
                    (fix (* (+ 1
                               (* (+ (fix (* (+ 1 (fix v0)) 1)) -1)
                                  (/ g1))
                               -640)
                            g1))))))))
 (< (+ (a i phi0 v0 dv g1)
       (* (/ (expt 5 (+ -2 i)))
          (b-sum 1 (+ -2 i) v0 dv g1)))
    0))
  :hints (("Goal"
	   :use ((:instance stupid-proof
			    (a (integerp (+ -1 -1 i)))
			    (b (and (rationalp g1)
				    (rationalp v0)
				    (rationalp dv)
				    (rationalp phi0)))
			    (c (equal (+ -2 i) 1))
			    (d (and (equal g1 1/3200)
				    (<= 9/10 v0)
				    (<= v0 11/10)
				    (<= -1/8000 dv)
				    (<= dv 1/8000)
				    (<= 0 phi0)
				    (< phi0
				       (+ -1
					  (* (fix (+ 1 (fix (+ v0 dv))))
					     (/ (+ 1
						   (fix (* (+ 1
							      (* (+ (fix (* (+ 1 (fix v0)) 1)) -1)
								 (/ g1))
							      -640)
							   g1)))))))))
			    (e (< (+ (a (+ -1 i) phi0 v0 dv g1)
				     (* (/ (expt 5 (+ -2 -1 i)))
					(b-sum 1 (+ -2 -1 i) v0 dv g1)))
				  0))
			    (f (integerp (+ -1 i)))
			    (g (< (+ (a i phi0 v0 dv g1)
				     (* (/ (expt 5 (+ -2 i)))
					(b-sum 1 (+ -2 i) v0 dv g1)))
				  0))
			    (h (and (<= 3 (+ -1 i))
				    (<= (+ -1 i) 640)))
			    (i (integerp i))
			    (j (and (<= 2 (+ -1 -1 i))
				    (<= (+ -1 -1 i) 640)))
			    (l (and (<= 2 (+ -1 i))
				    (<= (+ -1 i) 640)
				    ))
			    (m (>= i 1)))))))

(defthm phi-2n+1-<-0-lemma-lemma2
  (implies (and (or (not (integerp i)) (< i 1))
              (integerp (+ -1 i))
              (rationalp g1)
              (rationalp v0)
              (rationalp dv)
              (rationalp phi0)
              (<= 2 (+ -1 i))
              (<= (+ -1 i) 640)
              (equal g1 1/3200)
              (<= 9/10 v0)
              (<= v0 11/10)
              (<= -1/8000 dv)
              (<= dv 1/8000)
              (<= 0 phi0)
              (< phi0
                 (+ -1
                    (* (fix (+ 1 (fix (+ v0 dv))))
                       (/ (+ 1
                             (fix (* (+ 1
                                        (* (+ (fix (* (+ 1 (fix v0)) 1)) -1)
                                           (/ g1))
                                        -640)
                                     g1))))))))
         (< (+ (a i phi0 v0 dv g1)
               (* (/ (expt 5 (+ -2 i)))
                  (b-sum 1 (+ -2 i) v0 dv g1)))
            0))
  :rule-classes nil)

(defthm phi-2n+1-<-0-lemma
  (implies (basic-params (1- i) 2 v0 dv g1 phi0)
	   (< (+ (A i phi0 v0 dv g1)
		 (* (B-expt i)
		    (B-sum 1 (- i 2) v0 dv g1))) 0))
  :hints (("Goal"
	   :do-not '(simplify)
	   :induct (B-sum 1 i v0 dv g1))
	  ("Subgoal *1/2"
	  :use ((:instance phi-2n+1-<-0-base-new)
		(:instance phi-2n+1-<-0-base-corollary-2)
		(:instance phi-2n+1-<-0-inductive-corollary-2)
		))
	  ("Subgoal *1/2''"
	   :use ((:instance phi-2n+1-<-0-lemma-lemma1)))
	  ("Subgoal *1/1'"
	   :use ((:instance phi-2n+1-<-0-lemma-lemma2)))
	  )
  )

(defthm phi-2n+1-<-0
  (implies (basic-params (1- i) 2 v0 dv g1 phi0)
	   (< (phi-2n-1 i phi0 v0 dv g1) 0))
  :hints (("Goal"
	   :use ((:instance phi-2n+1-<-0-lemma))
	   ))
  )

(defthm phi-2n-1-<-0
  (implies (basic-params n 3 v0 dv g1 phi0)
	   (< (phi-2n-1 n phi0 v0 dv g1) 0))
  :hints (("Goal"
	   :use ((:instance phi-2n+1-<-0
			    (i n))))))
)

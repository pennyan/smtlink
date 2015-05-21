(in-package "ACL2")
(include-book "global")

(deftheory before-arith (current-theory :here))
(include-book "arithmetic/top-with-meta" :dir :system)
(deftheory after-arith (current-theory :here))

(deftheory arithmetic-book-only (set-difference-theories (theory 'after-arith) (theory 'before-arith)))

;; for the clause processor to work
(include-book "../smtlink/SMT-connect")
(logic)
:set-state-ok t
:set-ignore-ok t
(tshell-ensure)

(local
 (progn
   (defun my-smtlink-expt-config ()
     (declare (xargs :guard t))
     (make-smtlink-config :dir-interface "../smtlink/z3_interface"
			  :dir-files    "z3\_files"
			  :SMT-module   "RewriteExpt"
			  :SMT-class    "to_smt_w_expt"
			  :smt-cmd      "python"
			  :dir-expanded "expanded"))
   (defattach smt-cnf my-smtlink-expt-config)))


;;:start-proof-tree

;; functions
;; n can be a rational value when c starts from non-integer value
(defun fdco (n v0 dv g1)
  (/ (* (mu) (+ 1 (* *alpha* (+ v0 dv)))) (+ 1 (* *beta* n g1))))

(defun B-term-expt (gamma h)
  (expt gamma (- h)))

(defun B-term-rest (h v0 dv g1)
  (- (* (mu) (/ (+ 1 (* *alpha* (+ v0 dv))) (+ 1 (* *beta* (+ (* h g1) (equ-c v0)))))) 1))

(defun B-term (h v0 dv g1 gamma)
  (* (B-term-expt gamma h) (B-term-rest h v0 dv g1)))

(defun B-sum (h_lo h_hi v0 dv g1 gamma)
  (declare (xargs :measure (if (or (not (integerp h_hi)) (not (integerp h_lo)) (< h_hi h_lo))
			       0
			       (1+ (- h_hi h_lo)))))
  (if (or (not (integerp h_hi)) (not (integerp h_lo)) (> h_lo h_hi))  0
      (+ (B-term h_hi v0 dv g1 gamma ) (B-term (- h_hi) v0 dv g1 gamma)
         (B-sum h_lo (- h_hi 1) v0 dv g1 gamma))))

(defun B-expt (gamma n)
  (expt gamma (- n 2)))

(defun B (n v0 dv g1 gamma)
  (* (B-expt gamma n)
     (B-sum 1 (- n 2) v0 dv g1 gamma)))

;; parameter list functions
(defmacro basic-params-equal (n n-value &optional (v0 'nil) (dv 'nil) (g1 'nil) (phi0 'nil) (other 'nil))
  (list 'and
	(append
	 (append
	  (append
	   (append (list 'and
			 (list 'integerp n))
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
	       (append
		(list 'and
		      (list 'equal n n-value))
		(if (equal g1 'nil) nil (list (list 'equal g1 '1/3200))))
	       (if (equal v0 'nil) nil (list (list '>= v0 '9/10))))
	      (if (equal v0 'nil) nil (list (list '<= v0 '11/10))))
	     (if (equal dv 'nil) nil (list (list '>= dv (list '- (list 'dv0))))))
	    (if (equal dv 'nil) nil (list (list '<= dv (list 'dv0)))))
	   (if (equal phi0 'nil) nil (list (list '>= phi0 '0))))
	  (if (equal phi0 'nil) nil (list (list '< phi0 (list '- (list 'fdco (list '1+ (list 'm '640 v0 g1)) v0 dv g1) '1)))))
	 (if (equal other 'nil) nil (list other)))))

(defmacro basic-params (n nupper &optional (v0 'nil) (dv 'nil) (g1 'nil) (phi0 'nil) (other 'nil))
  (list 'and
	(append
	 (append
	  (append
	   (append (list 'and
			 (list 'integerp n))
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
	       (append
		(append (list 'and
			     (list '>= n nupper))
			(list (list '<= n '640)))
		       (if (equal g1 'nil) nil (list (list 'equal g1 '1/3200))))
	       (if (equal v0 'nil) nil (list (list '>= v0 '9/10))))
	      (if (equal v0 'nil) nil (list (list '<= v0 '11/10))))
	     (if (equal dv 'nil) nil (list (list '>= dv (list '- (list 'dv0))))))
	    (if (equal dv 'nil) nil (list (list '<= dv (list 'dv0)))))
	   (if (equal phi0 'nil) nil (list (list '>= phi0 '0))))
	  (if (equal phi0 'nil) nil (list (list '< phi0 (list '- (list 'fdco (list '1+ (list 'm '640 v0 g1)) v0 dv g1) '1)))))
	 (if (equal other 'nil) nil (list other)))))

;  The theorem exported by this encapsulation is:
;    (< (+ (B-term h v0 dv g1) (B-term (- h) v0 dv g1)) 0)
;  Yan's proof manually expanded B-term to expose the calls to expt.
;    She then used her clause processor to show
;      (and (< 0 (expt (gamma) -h)) (<= (expt (gamma) (- h)) (/ 1 5)))
;    Note: it would have been cleaner to write (gamma) instead of (/ 1 5).
;    Yan then proved the main result for this encapsulation by stating it.
;    ACL2 does the function expansions and finds that they match the lemma
;    Yan had stated by doing the expansions herself.
;  My plan was to use my "improved" version of the clause processor to automatically find
;    instances of expt and generate the relevant facts for z3.  I collided with the
;    the subtleties of Z3.  My pre-processor generated the assertion
;        (<= (expt (gamma) -h) (gamma))
;    as an extra hypotheses but Z3 didn't use it as needed.  If I first ask Z3 to show
;        (implies extended-hyps new-hyp)
;    where new-hyp is the inequality mentioned above, and new-hyp is a clause of extended-hyps,
;    the proof goes through.  If I then ask z3 to prove the original theorem (in the same python
;    session), that works too!
;  I thought about ways to make the z3 approach less brittle.  In so doing I realized that Yan's
;    proof is a rather brute-force way to avoid an induction argument.  Looking at (B-term ...)
;    yields:
;        (B-term h v0 dv g1) -> (* (B-term-expt h) (B-term-rest h v0 dv g1))
;    Yan's argument is that if h > 0, then 
;        (and (>= (B-term-expt h)     (/ (gamma))) (< (B-term-rest h v0 dv g1) 0)
;             (<= (B-term-expt (- h)) (gamma))
;             (<= (* (gamma) (gamma) (B-term-rest (- h) v0 dv g1)) (B-term-rest h v0 dv g1)))
;    Of course, the messy algebra is handled by z3.  This approach requires an upper bound on h
;    to make sure that (B-term-rest (- h) v0 dv g1) stays small enough -- the denominator
;    decreases with increasing h.
;  I'm going to try an inductive proof.  The induction hypothesis is
;    (and (< (B-term h v0 dv g1) 0)
;         (> (B-term (- h) v0 dv g1) 0)
;         (> (- (B-term h v0 dv g1)) (B-term (- h) v0 dv g1)))

(defthm B-term-neg-mrg
  (implies (and (and (integerp h) (rationalp v0) (rationalp dv) (rationalp g1) (rationalp gamma))
  		(<= 1 h) (< 0 v0) (< 0 dv) (< 0 g1) (< (/ 10) gamma)
  		(< g1 (/ 8)) (< dv (* (/ 4) (/ *alpha* *beta*) g1))
                (< h  (/ (* 2 g1))) (< gamma (/ 2)))
	   (> (- (B-term h v0 dv g1 gamma)) (B-term (- h) v0 dv g1 gamma)))
    :hints
    (("Goal"
      :clause-processor
      (smtlink clause
	 '( (:expand ((:functions ((B-term rationalp)
				   (B-term-expt rationalp)
				   (B-term-rest rationalp)
				   (gamma rationalp)
				   (mu rationalp)
				   (equ-c rationalp)
				   (dv0 rationalp)))
		      (:expansion-level 1)))
	    (:uninterpreted-functions ((expt rationalp rationalp rationalp)))
	    (:python-file "B-term-neg-mrg")) ;;mktemp
	    state))))

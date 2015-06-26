(in-package "ACL2")
(include-book "std/util/define" :dir :system)
(include-book "misc/eval" :dir :system) ; Define must-succeed and must-fail macros.
(include-book "tools/bstar" :dir :system) 
(include-book "ihs/ihs-init" :dir :system) ; for disable-theory and enable-theory

(deftheory before-arith (current-theory :here))
(include-book "arithmetic-5/top" :dir :system)
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
     (make-smtlink-config :dir-interface "../../z3_interface"
			  :dir-files    "z3\_files"
			  :SMT-module   "RewriteExpt"
			  :SMT-class    "to_smt_w_expt"
			  :smt-cmd      "python"
			  :dir-expanded "expanded"))
   (defattach smt-cnf my-smtlink-expt-config)))


;;; some functions and bounds on parameters that we use throughout the proof
(defconst *g1-min* (/ 65536))	  ; g1 is the size of a 'step' in c, the control capacitance
(defconst *g1-max* (/ 8))         ;   Note: c is implicit in the model below with c = nc*g1
                                  ;   where nc is the digital control setting for c.

(defconst *g2* (- (/ 1/3200 5)))  ; g2 is the size of a 'step' in v, the control voltage

(defconst *Kt-min* (/ 2))         ; Kt is the 'time-gain' of the loop.  Kt=1 would be perfect
(defconst *Kt-max* (/ 9 10))      ;   time gain -- the old phase error completely cancelled
                                  ;   at the next cycle of fref

(defconst *ccode* 1)		  ; The target value for c.
(defconst *N-freq* 1)             ; the frequency multiplication factor of the DPLL.
(defconst *fref* 1)

(defconst *alpha* 1)		  ; *alpha* and *beta* are gain terms in the DCO model
(defconst *beta* 1)		  ; I (mrg) suspect these can be absorbed into other model parameters.
(defconst *f0* 1)
(defconst *vcenter* 1)		  ; presumably the value for v when (equal (equ-c *vcenter*) *ccode*)
				  ; but it's not used anywhere in the proof.  We should probably
				  ; delete it.

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


; mrg:  Yikes!  I suspect that I wrote *alpha* where I should have written *beta*
;   and vice-versa in the definition of dv-bound.  Right now, it doesn't matter
;   because *alpha* = *beta* = 1.  I'll check this more carefully when the revised
;   proof is complete (22 June 2015)
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
;  [see remarks about *alpha* and *beta* with hyp-fn-help -- they may be backwards
;    here if they're backwards there]
(defmacro hyp-macro (g1 Kt v0 dv)
  `(and (rationalp ,g1) (< *g1-min* ,g1) (< ,g1 *g1-max*)
        (rationalp ,Kt) (< *Kt-min* ,Kt) (< ,Kt *Kt-max*)
        (rationalp ,v0) (< 0 ,v0)
        (rationalp ,dv) (< (- (* (/ 4) (/ *alpha* *beta*) ,g1)) ,dv)
		        (< ,dv (* (/ 4) (/ *alpha* *beta*) ,g1))))


;; A few checks to get a warm fuzzy feeling that hyp-fn probably does what we intended
; mrg: If I messed up *alpha* and *beta* above, then the test cases here (i.e. tests 5, 7, and 8)
;   will need to be fixed.
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



; mu is a handy normalization term for the frequency terms that occur in the DPLL model.
;   In particular, the values of n and v0 need to satisfy
;     (equal (/ (+ 1 (* *alpha* (+ v0 dv))) (+ 1 (* *beta* n g1))))
;   for the DCO to be oscillating at the target frequency.
(define mu ()
  :returns (f rationalp)
  (/ *f0* (* *N-freq* *fref*)))

; fdco is the *normalized* frequency of the DCO -- it took me (mrg) a while to figure this out.
;   The frequency of the DCO is (* (/ (+ 1 (* *alpha* (+ v0 dv))) (+ 1 (* *beta* n g1))) f0)
;   The target frequency is (* *N-freq* *fref*).  Thus,
;     (* (/ (+ 1 (* *alpha* (+ v0 dv))) (+ 1 (* *beta* nc g1))) mu)
;   is 1 when the DCO is at the target frequency.  (fdco nc v0 dv g1) returns the quantity above.
(define fdco (nc v0 dv g1)
  :guard (and (rationalp nc) (hyp-fn (list :v0 v0 :dv dv :g1 g1)) (< -1 (* *beta* nc g1)))
  :returns (f rationalp :hyp :guard)
  (/ (* (mu) (1+ (* *alpha* (+ v0 dv)))) (1+ (* *beta* nc g1))))
 
; (equ-c v0) is the value of c (i.e. (* nc g1)) that sets the DCO
;   frequency to the target frequency given a control voltage of v0.
;   mrg: I'm guessing I can replace all instances of equ-c with equ-nc
(define equ-c (v0)
  :guard (hyp-fn (list :v0 v0))
  :returns (c rationalp :hyp :guard)
  (/ (1- (* (mu) (1+ (* *alpha* v0)))) *beta*))

; (equ-nc v0) is the value of nc that will sets the DCO frequency
;   to the target frequency given a control voltage of v0.
(define equ-nc (v0 g1)
  :guard (hyp-fn (list :v0 v0 :g1 g1))
  :returns (nc rationalp :hyp :guard)
  (/ (1- (* (mu) (1+ (* *alpha* v0)))) (* *beta* g1)))

; A simple theorem showing that equ-nc is the inverse of fdco for nc.
(defthm fdco-and-equ-nc
  (implies (and (hyp-fn (list :v0 v0 :g1 g1)) (equal nc (equ-nc v0 g1)))
  	   (equal (fdco nc v0 0 g1) 1))
  :hints(("Goal" :in-theory (enable fdco equ-nc mu))))

; (gamma Kt) is the attenuation factor for a PLL with time-gain Kt
; In other words, if the phase offset at one rising edge of phi-ref is delta-phi,
; then the phase offset at the next rising edge will be (* (gamma Kt) delta-phi)
; plus any additional phase change due to (- (/ fdco *N-freq*) fref)
(define gamma (Kt)
  :guard (hyp-fn (list :Kt Kt))
  :returns (g rationalp :hyp :guard)
  (- 1 Kt)
  ///
  (more-returns (g (and (< 0 g) (< g 1) (not (equal g 0))) :hyp :guard :name gamma-bounds)))

; (m nc-offset v0 g1) returns a value for nc that is nc-offset below the value
;   that would establish (equal (/ (fdco n v0 dv g1) *N-freq*) fref)
(define m (nc-offset v0 g1)
  :guard (and (integerp nc-offset) (hyp-fn (list :v0 v0 :g1 g1)))
  :returns (mm rationalp :hyp :guard)
  (- (equ-nc v0 g1) nc-offset))

(define dv0 ()
  :returns (_dv0 rationalp)
  (* -2 *g2*))

;;:start-proof-tree

(define nco-ok (nc-offset g1 v0)
  :guard (rational-listp (list g1 v0))
  :returns (ok atom)
  :enabled t
  (and (integerp nc-offset)
       (< 0 (+ (* *beta* g1 nc-offset) (* (mu) (1+ (* *alpha* v0)))))))

(define nco-list-ok (nco-list g1 v0)
  :guard (and (integer-listp nco-list) (rational-listp (list g1 v0)))
  :returns (ok atom)
  :enabled t
  (if (endp nco-list) t
      (and (nco-ok (car nco-list) g1 v0) (nco-list-ok (cdr nco-list) g1 v0))))


(define B-term-expt (Kt nco)
  :guard (and (integerp nco) (hyp-fn (list :Kt Kt)))
  :returns (x rationalp
              :hyp :guard
              :hints (("Goal" :use ((:instance rationalp-of-gamma)))))
  (expt (gamma Kt) (- nco)))

; I would prefer to use equ-nc here, but the z3 has a time-out when proving B-term-neg.
; In particular:
;     (* *beta* (+ (* g1 nco) (equ-c v0)))
;   = (* *beta* g1 (+ nco (equ-nc v0 g1)))
;   = (* *beta* g1 (m (- nco) v0 g1))
; I hope that I could redefine m to avoid the need to negate nco.
; I suspect this might be workable once Yan has revised smtlink to handle
; clauses with multiple disjuncts.  Then, I could prove an ACL2 rewrite rule that
; would convert the nice-to-write version and transform it into the expression
; that Z3 can handle.  I'll revisit this later.
(define B-term-rest (nco v0 dv g1)
  :guard (and (integerp nco) (hyp-fn (list :v0 v0 :dv dv :g1 g1)) (nco-ok nco g1 v0))
  :guard-hints(("Goal" :in-theory (enable equ-nc m mu)))
  :returns (x rationalp :hyp :guard
    :hints(("Goal" :in-theory (enable equ-nc m mu))))
  (1- (* (mu) (/ (1+ (* *alpha* (+ v0 dv)))
		 (1+ (* *beta* g1 (m (- nco) v0 g1)))))))


(define B-term (nco v0 dv g1 Kt)
  :guard (and (integerp nco) (hyp-fn (list :v0 v0 :dv dv :g1 g1 :Kt Kt)) (nco-ok nco g1 v0))
  :returns (x rationalp
              :hyp :guard
              :hints (("Goal"
	      	       :in-theory (disable rationalp-of-B-term-expt rationalp-of-B-term-rest)
                       :use ((:instance rationalp-of-B-term-expt)
                             (:instance rationalp-of-B-term-rest))))
              )
  (* (B-term-expt Kt nco) (B-term-rest nco v0 dv g1)))

(encapsulate() ; define B_sum
  (local (defthm lemma-1 ; needed for rationalp-of-B_sum
    (implies (and (integerp nco_lo) (integerp nco_hi) (<= 0 nco_lo) (<= nco_lo nco_hi)
    	          (hyp-fn (list :v0 v0 :g1 g1)))
             (< g1 (+ 1 v0 (* g1 nco_hi))))))

  (define B_sum (nco_lo nco_hi v0 dv g1 Kt)
    :guard (and (integerp nco_lo) (integerp nco_hi)
                (<= 0 nco_lo) (<= nco_lo (1+ nco_hi))
                (hyp-fn (list :v0 v0 :dv dv :g1 g1 :Kt Kt))
                (nco-list-ok (list nco_lo nco_hi (- nco_hi)) g1 v0)
                )
    :returns (x rationalp :hyp :guard)
    :measure (if (and (integerp nco_hi) (integerp nco_lo) (>= nco_hi nco_lo))
                 (1+ (- nco_hi nco_lo))
               0)
    (if (and (integerp nco_hi) (integerp nco_lo) (>= nco_hi nco_lo))
        (+ (B-term nco_hi v0 dv g1 Kt ) (B-term (- nco_hi) v0 dv g1 Kt)
           (B_sum nco_lo (- nco_hi 1) v0 dv g1 Kt))
      0)))

(define B-expt (Kt n)
  :guard (and (integerp n) (hyp-fn (list :Kt Kt)))
  :returns (x rationalp
              :hyp :guard
              :hints (("Goal"
                       :use ((:instance rationalp-of-gamma))))
              )
  (expt (gamma Kt) (- n 2)))


(define B (nco v0 dv g1 Kt)
  :guard (and (integerp nco) (<= 2 nco) (hyp-fn (list :v0 v0 :dv dv :g1 g1 :Kt Kt))
              (nco-list-ok (list 1 (- 2 nco)) g1 v0))
  :returns (x rationalp
              :hyp :guard
              :hints (("Goal"
                       :use ((:instance rationalp-of-B-expt (n nco))
                             (:instance rationalp-of-B_sum
                                        (nco_lo 1)
                                        (nco_hi (- nco 2)))))))
  (* (B-expt Kt nco)
     (B_sum 1 (- nco 2) v0 dv g1 Kt)))

(define smt-std-hint (clause-name)
  :guard (stringp clause-name)
  `( (:expand ((:functions ( (A rationalp)
                             (B-term rationalp)
			     (B-term-expt rationalp)
			     (B-term-rest rationalp)
			     (dv0 rationalp)
			     (delta rationalp)
			     (delta-3 rationalp)
			     (equ-nc rationalp)
			     (fdco rationalp)
			     (gamma rationalp)
			     (m rationalp)
			     (mu rationalp)
			     (phi-2n-1 rationalp)))
	       (:expansion-level 1)))
     (:hypothesize ((equal (* g1 (+ (* v0 (/ g1)) h)) (+ v0 (* g1 h)))))
     (:uninterpreted-functions ((expt rationalp rationalp rationalp)))
     (:python-file ,clause-name)))

(encapsulate () ; defthm B-term-neg
  (local (in-theory (enable B-term m equ-nc gamma dv0)))
  (defthm B-term-neg
    (implies (and (integerp h) (<= 1 h) (< h (/ (* 2 g1)))
                  (hyp-macro g1 Kt v0 dv))
             (< (+ (B-term h v0 dv g1 Kt) (B-term (- h) v0 dv g1 Kt)) 0))
    :hints (
            ("Goal"
             :in-theory (e/d (B-term B-term-expt B-term-rest mu equ-c gamma dv0))
             :clause-processor
             (smtlink-custom-config clause (smt-std-hint "B-term-neg") state))
            )
    :rule-classes :linear)
  )

; B_sum-neg: show that the sum of a bunch of B-term pairs is negative.
;   This is a trivial induction proof that the sum of a bunch of negative values is negatoive.
;   We need B-term-neg to know that the terms in the sum are individually negative.
; B-term-neg gets a 'non-rec' warning.  I suspect that's why I need to disable it and
;   then specify a particular instance in the proof for B_sum-neg below.
;   On the other hand, I wonder if we could get a "computed hint" or similar to recognize
;   when the smtlink clause processor is applicable, and use it automatically.
;   In that case, we might not need to explicitly state and prove B-term-neg.
(defthm B_sum-neg
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
	 (:use ((:hypo ((B_sum-neg)))))) state))))


(encapsulate () ; define A
 (local (in-theory (enable m equ-c equ-nc)))
 (local (defthm lemma-1
   (implies (and (integerp nnco) (rationalp phi0) (rationalp v0) (rationalp dv)
		 (rationalp g1) (rationalp Kt)
		 (< 0 V0)
		 (< (* -1/4 G1) DV)
		 (< DV (* 1/4 G1))
		 (< 1/65536 G1)
		 (< G1 1/8)
		 (< 1/2 KT)
		 (< KT 9/10)
		 (< (* G1 NNCO) 1))
	    (and (RATIONALP (EXPT (GAMMA KT) (+ -1 (* 2 NNCO))))
		 (RATIONALP (EXPT (GAMMA KT) (+ -2 (* 2 NNCO))))
		 (RATIONALP (EXPT (GAMMA KT) (+ -3 (* 2 NNCO))))
		 (RATIONALP (FDCO (+ (- NNCO) (* (/ G1) V0)) V0 DV G1))
		 (RATIONALP (FDCO (1+ (m nnco v0 g1)) V0 DV G1))
		 ))
   :hints(("Goal" :in-theory (enable gamma)))))

 (local (defthm lemma-2
   (implies (and (rationalp e1) ; (EXPT (GAMMA KT) (+ -1 (* 2 NNCO)))
		 (rationalp e2) ; (EXPT (GAMMA KT) (+ -2 (* 2 NNCO)))
		 (rationalp e3) ; (EXPT (GAMMA KT) (+ -3 (* 2 NNCO)))
		 (rationalp f0) ; (FDCO (m nnco v0 g1) V0 DV G1)
		 (rationalp f1) ; (FDCO (+ 1 (- NNCO) (* (/ G1) V0)) V0 DV G1)
		 (rationalp phi0))
	     (rationalp (+ (- e2) (- e3) (* phi0 (- e1)) (* e2 f0) (* e3 f1))))))

 (local (defthm lemma-3
   (implies (and (integerp nnco) (rationalp phi0) (rationalp v0) (rationalp dv)
		 (rationalp g1) (rationalp Kt)
		 (< 0 V0)
		 (< (* -1/4 G1) DV)
		 (< DV (* 1/4 G1))
		 (< 1/65536 G1)
		 (< G1 1/8)
		 (< 1/2 KT)
		 (< KT 9/10)
		 (< (* G1 NNCO) 1))
	    (rationalp (+ (* (expt (gamma Kt) (- (* 2 nnco) 1)) phi0)
			  (* (expt (gamma Kt) (- (* 2 nnco) 2))
			     (- (fdco (m nnco v0 g1) v0 dv g1) 1))
			  (* (expt (gamma Kt) (- (* 2 nnco) 3))
			     (- (fdco (1+ (m nnco v0 g1)) v0 dv g1) 1)))))
   :hints(("Goal"
     :in-theory (disable lemma-1 lemma-2)
     :use(
       (:instance lemma-1 (nnco nnco) (phi0 phi0) (v0 v0) (dv dv) (g1 g1) (Kt Kt))
       (:instance lemma-2
	   (e1 (EXPT (GAMMA KT) (+ -1 (* 2 NNCO))))
	   (e2 (EXPT (GAMMA KT) (+ -2 (* 2 NNCO))))
	   (e3 (EXPT (GAMMA KT) (+ -3 (* 2 NNCO))))
	   (f0 (FDCO (+ (- NNCO) (* (/ G1) V0)) V0 DV G1))
	   (f1 (FDCO (+ 1 (- NNCO) (* (/ G1) V0)) V0 DV G1))))))))

 (define A (nnco phi0 v0 dv g1 Kt)
   :guard (and (integerp nnco) (rationalp phi0) (rationalp v0) (rationalp dv)
	       (rationalp g1) (rationalp Kt)
	       (hyp-fn (list :v0 v0 :dv dv :g1 g1 :Kt Kt))
	       (< (* g1 nnco) 1)
	       (nco-ok (- nnco) g1 v0) (nco-ok (1+ (- nnco)) g1 v0))
   :returns (aa rationalp :hyp :guard
     :hints(("Goal"
       :in-theory (disable equ-c equ-nc fdco gamma m mu lemma-1 lemma-2 lemma-3)
      :use(
	(:instance lemma-3 (nnco nnco) (phi0 phi0) (v0 v0) (dv dv) (g1 g1) (Kt Kt))))))
   (+ (* (expt (gamma Kt) (- (* 2 nnco) 1)) phi0)
      (* (expt (gamma Kt) (- (* 2 nnco) 2))
	 (- (fdco (m nnco v0 g1) v0 dv g1) 1))
      (* (expt (gamma Kt) (- (* 2 nnco) 3))
	 (- (fdco (1+ (m nnco v0 g1)) v0 dv g1) 1)))))

(defthm stop-here nil)

(defun phi-2n-1 (n phi0 v0 dv g1 Kt)
  :guard (and (integerp nn) (rationalp phi0) (rationalp v0) (ratinalp dv)
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
    ; try replacing the hypotheses here with hyp-macro
    (implies (and (integerp n) (<= 3 n) (< n (/ (* 2 g1)))
                  (hyp-macro g1 Kt v0 dv))
             (equal (delta n v0 dv g1 Kt) (delta-3 n v0 dv g1 Kt)))
    :hints (("Goal" :in-theory (enable delta delta-3 equ-c fdco mu gamma m A phi-2n-1)
		    :clause-processor
		      (smtlink-custom-config clause (smt-std-hint "delta-rewrite-5") state)))))


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

;; (encapsulate ()

;; (local
;; (defthm delta-<-0-lemma1-lemma
;;   (implies (basic-params n 3 v0 dv g1)
;; 	   (implies (< (+ (* (expt (gamma) 2)
;; 			     (- (fdco (1- (m n v0 g1)) v0 dv g1)
;; 				(fdco (m n v0 g1) v0 dv g1)))
;; 			  (* (expt (gamma) 1)
;; 			     (- (fdco (m n v0 g1) v0 dv g1)
;; 				(fdco (1+ (m n v0 g1)) v0 dv g1)))
;; 			  (* (expt (gamma) (- 2 (* 2 n)))
;; 			     (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
;; 				   (1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0))))) 1))
;; 			  (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
;; 				(1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1))
;; 		       0)
;; 		    (< (* (expt (gamma) (+ -1 n -1 n))
;; 			  (+ (* (expt (gamma) 2)
;; 				(- (fdco (1- (m n v0 g1)) v0 dv g1)
;; 				   (fdco (m n v0 g1) v0 dv g1)))
;; 			     (* (expt (gamma) 1)
;; 				(- (fdco (m n v0 g1) v0 dv g1)
;; 				   (fdco (1+ (m n v0 g1)) v0 dv g1)))
;; 			     (* (expt (gamma) (- 2 (* 2 n)))
;; 				(- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
;; 				      (1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0))))) 1))
;; 			     (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
;; 				   (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1)))
;; 		       0)))
;;   :hints (("Goal"
;; 	   :clause-processor
;; 	   (my-clause-processor clause
;; 				'( (:expand ((:functions ((m integerp)
;; 							  (gamma rationalp)
;; 							  (mu rationalp)
;; 							  (equ-c rationalp)
;; 							  (fdco rationalp)
;; 							  (dv0 rationalp)))
;; 					     (:expansion-level 1)))
;; 				  (:python-file "delta-smaller-than-0-lemma1-lemma")
;; 				  (:let ((expt_gamma_2n
;; 					  (expt (gamma) (* 2 n))
;; 					   rationalp)
;; 					 (expt_gamma_2n_minus_1
;; 					  (expt (gamma) (- (* 2 n) 1))
;; 					   rationalp)
;; 					 (expt_gamma_2n_minus_2
;; 					  (expt (gamma) (+ -1 n -1 n))
;; 					   rationalp)
;; 					 (expt_gamma_2
;; 					  (expt (gamma) 2)
;; 					   rationalp)
;; 					 (expt_gamma_1
;; 					  (expt (gamma) 1)
;; 					   rationalp)
;; 					 (expt_gamma_2_minus_2n
;; 					  (expt (gamma) (- 2 (* 2 n)))
;; 					   rationalp)
;; 					 ))
;; 				  (:hypothesize ((> expt_gamma_2n_minus_2 0))))))))
;; )

;; (local
;; (defthm delta-<-0-lemma1
;;   (implies (basic-params n 3 v0 dv g1)
;; 	   (implies (< (delta-3-inside n v0 dv g1) 0)
;; 		    (< (delta-3 n v0 dv g1) 0))))
;; )

;; (local
;; (defthm delta-<-0-lemma2-lemma
;;   (implies (basic-params n 3 v0 dv g1)
;; 	   (implies (< (/ (+ (* (expt (gamma) 2)
;; 				(- (fdco (1- (m n v0 g1)) v0 dv g1)
;; 				   (fdco (m n v0 g1) v0 dv g1)))
;; 			     (* (expt (gamma) 1)
;; 				(- (fdco (m n v0 g1) v0 dv g1)
;; 				   (fdco (1+ (m n v0 g1)) v0 dv g1)))
;; 			     (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
;; 				   (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1))
;; 			  (- 1
;; 			     (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
;; 				(1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0)))))))
;; 		       (expt (gamma) (- 2 (* 2 n))))
;; 		    (< (+ (* (expt (gamma) 2)
;; 			     (- (fdco (1- (m n v0 g1)) v0 dv g1)
;; 				(fdco (m n v0 g1) v0 dv g1)))
;; 			  (* (expt (gamma) 1)
;; 			     (- (fdco (m n v0 g1) v0 dv g1)
;; 				(fdco (1+ (m n v0 g1)) v0 dv g1)))
;; 			  (* (expt (gamma) (- 2 (* 2 n)))
;; 			     (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
;; 				   (1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0))))) 1))
;; 			  (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
;; 				(1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1))
;; 		       0)))
;;   :hints (("Goal"
;; 	   :clause-processor
;; 	   (my-clause-processor clause
;; 				'( (:expand ((:functions ((m integerp)
;; 							  (gamma rationalp)
;; 							  (mu rationalp)
;; 							  (equ-c rationalp)
;; 							  (fdco rationalp)
;; 							  (dv0 rationalp)))
;; 					     (:expansion-level 1)))
;; 				  (:python-file "delta-smaller-than-0-lemma2-lemma")
;; 				  (:let ((expt_gamma_2n
;; 					  (expt (gamma) (* 2 n))
;; 					   rationalp)
;; 					 (expt_gamma_2n_minus_1
;; 					  (expt (gamma) (- (* 2 n) 1))
;; 					   rationalp)
;; 					 (expt_gamma_2n_minus_2
;; 					  (expt (gamma) (+ -1 n -1 n))
;; 					   rationalp)
;; 					 (expt_gamma_2
;; 					  (expt (gamma) 2)
;; 					   rationalp)
;; 					 (expt_gamma_1
;; 					  (expt (gamma) 1)
;; 					   rationalp)
;; 					 (expt_gamma_2_minus_2n
;; 					  (expt (gamma) (- 2 (* 2 n)))
;; 					   rationalp)
;; 					 ))
;; 				  (:hypothesize ((> expt_gamma_2_minus_2n 0))))))))
;; )

;; (local
;; (defthm delta-<-0-lemma2
;;   (implies (basic-params n 3 v0 dv g1)
;; 	   (implies (< (delta-3-inside-transform n v0 dv g1)
;; 		       (expt (gamma) (- 2 (* 2 n))))
;; 		    (< (delta-3-inside n v0 dv g1) 0)))
;;   :hints (("Goal"
;; 	   :use ((:instance delta-<-0-lemma2-lemma)))))
;; )

;; (local
;; ;; This is for proving 2n < gamma^(2-2n)
;; (defthm delta-<-0-lemma3-lemma1
;;   (implies (and (integerp k)
;; 		(>= k 6))
;; 	   (< k (expt (/ (gamma)) (- k 2)))))
;; )

;; (local
;;  (defthm delta-<-0-lemma3-lemma2-stupidlemma
;;    (implies (basic-params n 3)
;; 	    (>= n 3))))

;; (local
;;  (defthm delta-<-0-lemma3-lemma2-stupidlemma-omg
;;    (implies (and (rationalp a) (rationalp b) (>= a b))
;; 	    (>= (* 2 a) (* 2 b)))))

;; (local
;;  (defthm delta-<-0-lemma3-lemma2-lemma1
;;    (implies (basic-params n 3)
;; 	    (>= (* 2 n) 6))
;;    :hints (("Goal"
;; 	    :use ((:instance delta-<-0-lemma3-lemma2-stupidlemma)
;; 		  (:instance delta-<-0-lemma3-lemma2-stupidlemma-omg
;; 			     (a n)
;; 			     (b 3))
;; 		  ))))
;;  )

;; (local
;; (defthm delta-<-0-lemma3-lemma2
;;   (implies (basic-params n 3)
;; 	   (< (* 2 n)
;; 	      (expt (/ (gamma)) (- (* 2 n) 2))))
;;   :hints (("Goal"
;; 	   :use ((:instance delta-<-0-lemma3-lemma1
;; 			   (k (* 2 n)))
;; 		 (:instance delta-<-0-lemma3-lemma2-lemma1))))
;;   :rule-classes :linear)
;; )

;; (local
;; (defthm delta-<-0-lemma3-lemma3-stupidlemma
;;   (equal (expt a n) (expt (/ a) (- n))))
;; )

;; (local
;; (defthm delta-<-0-lemma3-lemma3
;;   (implies (basic-params n 3)
;; 	   (equal (expt (/ (gamma)) (- (* 2 n) 2))
;; 		  (expt (gamma) (- 2 (* 2 n)))))
;;   :hints (("Goal"
;; 	   :use ((:instance delta-<-0-lemma3-lemma3-stupidlemma
;; 			    (a (/ (gamma)))
;; 			    (n (- (* 2 n) 2))))
;; 	   :in-theory (disable delta-<-0-lemma3-lemma3-stupidlemma))))
;; )

;; (local
;; (defthm delta-<-0-lemma3-lemma4-stupidlemma
;;   (implies (and (< a b) (equal b c)) (< a c)))
;; )

;; (local
;; (defthm delta-<-0-lemma3-lemma4
;;   (implies (basic-params n 3)
;; 	   (< (* 2 n)
;; 	      (expt (gamma) (- 2 (* 2 n)))))
;;   :hints (("Goal"
;; 	   :do-not '(preprocess simplify)
;; 	   :use ((:instance delta-<-0-lemma3-lemma2)
;; 		 (:instance delta-<-0-lemma3-lemma3)
;; 		 (:instance delta-<-0-lemma3-lemma4-stupidlemma
;; 			    (a (* 2 n))
;; 			    (b (expt (/ (gamma)) (- (* 2 n) 2)))
;; 			    (c (expt (gamma) (- 2 (* 2 n))))))
;; 	   :in-theory (disable delta-<-0-lemma3-lemma2
;; 			       delta-<-0-lemma3-lemma3
;; 			       delta-<-0-lemma3-lemma4-stupidlemma)))
;;   :rule-classes :linear)
;; )

;; (local
;; (defthm delta-<-0-lemma3
;;   (implies (basic-params n 3 v0 dv g1)
;; 	   (implies (< (/ (+ (* (expt (gamma) 2)
;; 				(- (fdco (1- (m n v0 g1)) v0 dv g1)
;; 				   (fdco (m n v0 g1) v0 dv g1)))
;; 			     (* (expt (gamma) 1)
;; 				(- (fdco (m n v0 g1) v0 dv g1)
;; 				   (fdco (1+ (m n v0 g1)) v0 dv g1)))
;; 			     (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
;; 				   (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1))
;; 			  (- 1
;; 			     (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
;; 				(1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0)))))))
;; 		       (* 2 n))
;; 		    (< (/ (+ (* (expt (gamma) 2)
;; 				(- (fdco (1- (m n v0 g1)) v0 dv g1)
;; 				   (fdco (m n v0 g1) v0 dv g1)))
;; 			     (* (expt (gamma) 1)
;; 				(- (fdco (m n v0 g1) v0 dv g1)
;; 				   (fdco (1+ (m n v0 g1)) v0 dv g1)))
;; 			     (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
;; 				   (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1))
;; 			  (- 1
;; 			     (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
;; 				(1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0)))))))
;; 		       (expt (gamma) (- 2 (* 2 n))))))
;;   :hints (("Goal"
;; 	   :clause-processor
;; 	   (my-clause-processor clause
;; 				'( (:expand ((:functions ((m integerp)
;; 							  (gamma rationalp)
;; 							  (mu rationalp)
;; 							  (equ-c rationalp)
;; 							  (fdco rationalp)
;; 							  (dv0 rationalp)))
;; 					     (:expansion-level 1)))
;; 				  (:python-file "delta-smaller-than-0-lemma3")
;; 				  (:let ((expt_gamma_2n
;; 					  (expt (gamma) (* 2 n))
;; 					   rationalp)
;; 					 (expt_gamma_2n_minus_1
;; 					  (expt (gamma) (- (* 2 n) 1))
;; 					   rationalp)
;; 					 (expt_gamma_2n_minus_2
;; 					  (expt (gamma) (+ -1 n -1 n))
;; 					   rationalp)
;; 					 (expt_gamma_2
;; 					  (expt (gamma) 2)
;; 					   rationalp)
;; 					 (expt_gamma_1
;; 					  (expt (gamma) 1)
;; 					   rationalp)
;; 					 (expt_gamma_2_minus_2n
;; 					  (expt (gamma) (- 2 (* 2 n)))
;; 					   rationalp))
;; 					 )
;; 				  (:hypothesize ((< (* 2 n) expt_gamma_2_minus_2n)))
;; 				  (:use ((:type ())
;; 				   	 (:hypo ((delta-<-0-lemma3-lemma4)))
;; 				   	 (:main ())))
;; 				  ))
;; 	   :in-theory (disable delta-<-0-lemma3-lemma1
;; 	   		       delta-<-0-lemma3-lemma3-stupidlemma
;; 	   		       delta-<-0-lemma3-lemma2
;; 	   		       delta-<-0-lemma3-lemma3
;; 			       delta-<-0-lemma3-lemma4-stupidlemma)
;; 	   )))
;; )

;; (local
;; (defthm delta-<-0-lemma4
;;   (implies (basic-params n 3 v0 dv g1)
;; 	   (< (/ (+ (* (expt (gamma) 2)
;; 		       (- (fdco (1- (m n v0 g1)) v0 dv g1)
;; 			  (fdco (m n v0 g1) v0 dv g1)))
;; 		    (* (expt (gamma) 1)
;; 		       (- (fdco (m n v0 g1) v0 dv g1)
;; 			  (fdco (1+ (m n v0 g1)) v0 dv g1)))
;; 		    (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
;; 			  (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1))
;; 		 (- 1
;; 		    (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
;; 		       (1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0)))))))
;; 	      (* 2 n)))
;;   :hints (("Goal"
;; 	   :clause-processor
;; 	   (my-clause-processor clause
;; 				'( (:expand ((:functions ((m integerp)
;; 							  (gamma rationalp)
;; 							  (mu rationalp)
;; 							  (equ-c rationalp)
;; 							  (fdco rationalp)
;; 							  (dv0 rationalp)))
;; 					     (:expansion-level 1)))
;; 				  (:python-file "delta-smaller-than-0-lemma4")
;; 				  (:let ((expt_gamma_2n
;; 					  (expt (gamma) (* 2 n))
;; 					   rationalp)
;; 					 (expt_gamma_2n_minus_1
;; 					  (expt (gamma) (- (* 2 n) 1))
;; 					   rationalp)
;; 					 (expt_gamma_2n_minus_2
;; 					  (expt (gamma) (+ -1 n -1 n))
;; 					   rationalp)
;; 					 (expt_gamma_2
;; 					  (expt (gamma) 2)
;; 					   rationalp)
;; 					 (expt_gamma_1
;; 					  (expt (gamma) 1)
;; 					   rationalp)
;; 					 (expt_gamma_2_minus_2n
;; 					  (expt (gamma) (- 2 (* 2 n)))
;; 					   rationalp))
;; 					 )
;; 				  (:hypothesize ((equal expt_gamma_1 1/5)
;; 						 (equal expt_gamma_2 1/25)))))
;; 	   :in-theory (disable delta-<-0-lemma3-lemma1
;; 	   		       delta-<-0-lemma3-lemma3-stupidlemma
;; 	   		       delta-<-0-lemma3-lemma2
;; 	   		       delta-<-0-lemma3-lemma3
;; 			       delta-<-0-lemma3-lemma4-stupidlemma
;; 			       delta-<-0-lemma3-lemma4))))
;; )

(defthm stop-here nil)

(defthm delta-<-0-lemma-1
  (implies (and (hyp-macro g1 Kt v0 dv) (integerp n) (<= 3 n) (< (* 2 n g1) (+ 1 0)))
           (equal (delta n v0 dv g1 Kt)
	   	  (+ (/ (* (gamma Kt) (gamma Kt) (+ 1 v0 dv) g1)
		        (* (+ 1 v0 (* (- g1) (1+ N))) (+ 1 v0 (* (- g1) n))))
		     (/ (* (gamma Kt) (+ 1 v0 dv) g1)
		        (* (+ 1 v0 (* (- g1) n)) (+ 1 v0 (* (- g1) (1- n)))))
		     (1- (/ (+ 1 v0 dv) (+ 1 v0 (* (- g1) (1- n)))))
		     (* (expt (gamma Kt) (+ (* -2 N) 2))
		        (+ -1 (/ (+ 1 v0 dv) (+ 1 v0 (* g1 (1- n)))))))))
  :hints(("Goal"
    :in-theory (enable delta)
    :clause-processor
    (smtlink-custom-config clause (smt-std-hint "delta-lt-0-lemma-1") state))))
      
(defthm delta-<-0
  (implies (and (integerp n) (<= 3 n) (< n (/ (* 2 g1)))
                (hyp-macro g1 Kt v0 dv))
           (< (delta n v0 dv g1 Kt) 0))
  :hints (("Goal"
           :in-theory (enable delta equ-c fdco mu gamma m)
           :clause-processor
           (smtlink-custom-config clause (smt-std-hint "delta_smaller_than_0") state)))
     )

;;) ;; delta < 0 thus is proved

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
		     (B_sum 1 (- n 1) v0 dv g1)))))
)

(local
(defthm split-phi-2n+1-lemma2-lemma2
  (implies (basic-params n 3 v0 dv g1)
	   (equal (B (+ n 1) v0 dv g1)
		  (* (expt (gamma) (- n 1))
		     (+ (B-term (- n 1) v0 dv g1)
			(B-term (- (- n 1)) v0 dv g1)
			(B_sum 1 (- n 2) v0 dv g1))))))
)

(local
(defthm split-phi-2n+1-lemma2-lemma3
  (implies (basic-params n 3 v0 dv g1)
	   (equal (B (+ n 1) v0 dv g1)
		  (+ (* (expt (gamma) (- n 1))
			(B_sum 1 (- n 2) v0 dv g1))
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
			(B_sum 1 (- n 2) v0 dv g1))
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
		    (B_sum 1 (- i 2) v0 dv g1))) 0))
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
		    (B_sum 1 (- i 2) v0 dv g1))) 0))
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
		    (B_sum 1 (- i 2) v0 dv g1))) 0))
  :hints (("Goal"
	   :do-not '(simplify)
	   :induct (B_sum 1 i v0 dv g1))
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

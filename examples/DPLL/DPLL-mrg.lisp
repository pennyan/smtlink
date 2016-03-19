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
			  :smt-cmd      "python"))
   (defattach smt-cnf my-smtlink-expt-config)))


;;; some functions and bounds on parameters that we use throughout the proof
(defconst *g1-min* (/ 65536))	  ; g1 is the size of a 'step' in c, the control capacitance
(defconst *g1-max* (/ 8))         ;   Note: c is implicit in the model below with c = nc*g1
                                  ;   where nc is the digital control setting for c.

(defconst *g2* (- (/ 1/3200 5)))  ; g2 is the size of a 'step' in v, the control voltage

(defconst *Kt-min* (/ 2))         ; Kt is the 'time-gain' of the loop.  Kt=1 would be perfect
(defconst *Kt-max* (/ 9 10))      ;   time gain -- the old phase error completely cancelled
                                  ;   at the next cycle of fref

(defconst *v-min* 0)		  ; minimum value for the control voltage
(defconst *v-max* 3)		  ; maximum value for the control voltage

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
	              ((equal name :v0) (and (rationalp var) (< *v-min*  var) (< var *v-max*)))
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
        (rationalp ,v0) (< *v-min* ,v0)   (< ,v0 *v-max*)
        (rationalp ,dv) (< (- (* (/ 4)   (/ *alpha* *beta*) ,g1)) ,dv)
		        (< ,dv (* (/ 4)  (/ *alpha* *beta*) ,g1))))


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
                          (and (rationalp v0) (< *v-min* v0) (< v0 *v-max*)))))
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
;   that would establish (equal (fdco n v0 dv g1) (* *N-freq* *fref*))
(define m (nc-offset v0 g1)
  :guard (and (integerp nc-offset) (hyp-fn (list :v0 v0 :g1 g1)))
  :returns (mm rationalp :hyp :guard)
  (- (equ-nc v0 g1) nc-offset))

(define dv0 ()
  :returns (_dv0 rationalp) (* -2 *g2*)) 
;;:start-proof-tree

(define smt-std-hint (clause-name)
  :guard (stringp clause-name)
  `( (:expand ((:functions ( (A rationalp)
                             (B-term rationalp)
			     (B-term-expt rationalp)
			     (B-term-rest rationalp)
			     (dv0 rationalp)
			     (delta rationalp)
			     (delta-a rationalp)
			     (delta-b rationalp)
			     (equ-c rationalp)
			     (equ-nc rationalp)
			     (fdco rationalp)
			     (gamma rationalp)
			     (m rationalp)
			     (mu rationalp)
			     (phi-2n-1 rationalp)
			     (plus rationalp)
			     (aa rationalp)
			     (bb rationalp)))
	       (:expansion-level 1)))
     (:uninterpreted-functions ((expt rationalp rationalp rationalp)))
     (:python-file ,clause-name)))

(define nco-ok (nc-offset g1 v0)
  :guard (rational-listp (list g1 v0))
  :returns (ok atom)
  :enabled t
  (and (integerp nc-offset)
       (< 0 (+ (* *beta* g1 nc-offset) (* (mu) (1+ (* *alpha* v0)))))))

(defthm monotonicity-of-nco-ok
  (implies (and (hyp-macro g1 Kt v0 dv) (integerp nco1) (integerp nco2) (< nco1 nco2)
		(nco-ok nco1 g1 v0))
	   (nco-ok nco2 g1 v0))
  :hints(("Goal'''"
    :clause-processor
    (smtlink-custom-config clause (smt-std-hint "monotonicity-of-nco-ok") ))))

(defthm rationalp-of-m-and-fdco
  (implies (and (hyp-macro g1 Kt v0 dv) (integerp n) (nco-ok (- n) g1 v0))
	   (and (< -1 (* g1 *beta* (m n v0 g1)))
	        (rationalp (fdco (m n v0 g1) v0 dv g1))))
  :hints(("Goal" :in-theory (enable fdco m equ-nc equ-c gamma))))

(define nco-list-ok (nco-list g1 v0)
  :guard (and (integer-listp nco-list) (rational-listp (list g1 v0)))
  :returns (ok atom)
  :enabled t
  (if (endp nco-list) t
      (and (nco-ok (car nco-list) g1 v0) (nco-list-ok (cdr nco-list) g1 v0))))

; a handy special case when the base of the exponent is rational
; I could probably generalize this to the case where
;   (and (equal x 0) (< 0 n))
; but I don't seem to need that version here.
(defthm rationalp-of-expt
  (implies (and (rationalp x) (not (equal 0 x)) (integerp n)) (rationalp (expt x n))))

(defthm expt-gamma-Kt-is-positive
  (implies (and (integerp n) (hyp-fn (list :Kt Kt))) (< 0 (expt (gamma Kt) n)))
  :hints(("Goal"
    :in-theory (enable expt gamma))))

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
  :guard-hints(("Goal" :in-theory (enable equ-c mu)))
  :returns (x rationalp :hyp :guard
    :hints(("Goal" :in-theory (enable equ-c mu))))
  (1- (* (mu) (/ (1+ (* *alpha* (+ v0 dv)))
		 (1+ (* *beta* (+ (* g1 nco) (equ-c v0))))))))


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
             (< g1 (+ 1 v0 (* g1 nco_hi)))))) ; probably need some *alpha* and *beta* factors here

  (define B_sum (nco_lo nco_hi v0 dv g1 Kt)
    :guard (and (integerp nco_lo) (integerp nco_hi)
                (<= 0 nco_lo) (<= nco_lo (1+ nco_hi))
                (hyp-macro g1 Kt v0 dv)
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
              :hints (("Goal" :use ((:instance rationalp-of-gamma)))))
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

(defthm B-term-neg
  (implies (and (integerp h) (<= 1 h) (< h (/ (* 2 g1)))
		(hyp-macro g1 Kt v0 dv))
	   (< (+ (B-term h v0 dv g1 Kt) (B-term (- h) v0 dv g1 Kt)) 0))
    :hints (
      ("Goal"
	:in-theory (enable B-term B-term-expt B-term-rest mu equ-c gamma dv0)
	:clause-processor
	(smtlink-custom-config clause (smt-std-hint "B-term-neg") )))
    :rule-classes :linear)

; B_sum-neg: show that the sum of a bunch of B-term pairs is negative.
;   This is a trivial induction proof that the sum of a bunch of negative values is negative.
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

(defthm stop nil)

(defthm B-neg
  (implies (and (integerp n) (<= 3 n) (hyp-macro g1 Kt v0 dv)
                (< n (/ (* 2 g1)))) ; probably need a factor of *beta* here
	   (< (B n v0 dv g1 Kt) 0))
  :hints (
    ("Goal"
      :in-theory (enable B gamma B-expt)
      :clause-processor
      (smtlink-custom-config clause
	'( (:expand ((:functions ((B rationalp) (B-expt rationalp) (gamma rationalp)))
		     (:expansion-level 1)))
	   (:uninterpreted-functions (
	     (expt rationalp integerp rationalp)
	     (B_sum integerp integerp rationalp rationalp rationalp rationalp  rationalp)))
	   (:python-file "B-neg")
	   (:hypothesize ((< (B_sum 1 (+ -2 n) v0 dv g1 Kt) 0))))))
    ("Subgoal 2"
      :in-theory (enable hyp-fn)
      :use ((:instance B_sum-neg (n-minus-2 (+ -2 n)) (v0 v0) (dv dv) (g1 g1) (Kt Kt))))))

(encapsulate () ; define A
 (local (in-theory (enable gamma m equ-c equ-nc)))

 (local (defthm lemma-1
   (implies (rational-listp (list e1 e2 e3 f0 f1 phi0))
	    (rationalp (+ (- e2) (- e3) (* phi0 (- e1)) (* e2 f0) (* e3 f1))))))

 (local (defthm lemma-2
   (implies (and (integerp nnco) (rationalp phi0)
                 (hyp-macro g1 Kt v0 dv) (< (* g1 nnco) 1))
	    (rationalp (+ (* (expt (gamma Kt) (- (* 2 nnco) 1)) phi0)
			  (* (expt (gamma Kt) (- (* 2 nnco) 2))
			     (- (fdco (m nnco v0 g1) v0 dv g1) 1))
			  (* (expt (gamma Kt) (- (* 2 nnco) 3))
			     (- (fdco (1+ (m nnco v0 g1)) v0 dv g1) 1)))))
   :hints(("Goal"
     :in-theory (disable lemma-1)
     :use(
       (:instance lemma-1
	   (e1 (expt (gamma kt) (+ -1 (* 2 nnco))))
	   (e2 (expt (gamma kt) (+ -2 (* 2 nnco))))
	   (e3 (expt (gamma kt) (+ -3 (* 2 nnco))))
	   (f0 (fdco (+ (- nnco) (* (/ g1) v0)) v0 dv g1))
	   (f1 (fdco (+ 1 (- nnco) (* (/ g1) v0)) v0 dv g1))))))))

 (define A (nnco phi0 v0 dv g1 Kt)
   :guard (and (integerp nnco) (rationalp phi0)
	       (hyp-macro g1 Kt v0 dv) (< (* g1 nnco) 1))
   :returns (aa rationalp :hyp :guard
     :hints(("Goal"
       :in-theory (disable equ-c equ-nc fdco gamma m mu lemma-1 lemma-2)
       :use(
	 (:instance lemma-2 (nnco nnco) (phi0 phi0) (v0 v0) (dv dv) (g1 g1) (Kt Kt))))))
   (+ (* (expt (gamma Kt) (- (* 2 nnco) 1)) phi0)
      (* (expt (gamma Kt) (- (* 2 nnco) 2))
	 (- (fdco (m nnco v0 g1) v0 dv g1) 1))
      (* (expt (gamma Kt) (- (* 2 nnco) 3))
	 (- (fdco (1+ (m nnco v0 g1)) v0 dv g1) 1)))))

(define phi-2n-1 (nnco phi0 v0 dv g1 Kt)
  :guard (and (integerp nnco) (rationalp phi0) (<= 2 nnco) (hyp-macro g1 Kt v0 dv)
              (nco-list-ok (list 1 (- 2 nnco)) g1 v0) (< (* g1 nnco) 1))
  :returns (x rationalp :hyp :guard)
  (+ (A nnco phi0 v0 dv g1 Kt) (B nnco v0 dv g1 Kt)))

;; I suspect that I'll be able to delete delta-orig from this proof by the time I'm done.
(defun delta-orig (n v0 dv g1 Kt)
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

(encapsulate () ; define delta delta-a delta-b aa bb
  (local (defthm lemma-1
    (implies (rational-listp (list a b c))
             (and (rationalp (+ (+ (* a b)) (* a c))) (rationalp (+ (- (* a b)) (* a c)))))))

  (define delta-a (nco v0 dv g1 Kt)
    :guard (and (hyp-fn (list :g1 g1 :Kt Kt :v0 v0 :dv dv))
                (integerp nco) (nco-ok (- -1 nco) g1 v0))
    :guard-hints(("Goal"
      :in-theory (disable rationalp-of-m-and-fdco)
      :use(
        (:instance rationalp-of-m-and-fdco (g1 g1) (Kt Kt) (v0 v0) (dv dv) (n nco))
        (:instance rationalp-of-m-and-fdco (g1 g1) (Kt Kt) (v0 v0) (dv dv) (n (+ nco 1)))) ))
    :returns (d rationalp :hyp :guard)
    (* (expt (gamma Kt) nco)
       (- (fdco (m (+ nco 1) v0 g1) v0 dv g1)
	  (fdco (m nco v0 g1) v0 dv g1))))

  (define aa (nco v0 dv g1 Kt)
    :guard (and (hyp-fn (list :g1 g1 :Kt Kt :v0 v0 :dv dv))
                (integerp nco) (nco-ok (- -1 nco) g1 v0))
    :guard-hints (("Goal" :nonlinearp t))
    :returns (a-sum rationalp :hyp :guard
      :hints(("Goal"
	:nonlinearp t
	:use(
	  (:instance rationalp-of-delta-a (nco nco) (v0 v0) (dv dv) (g1 g1) (Kt Kt))
	  (:instance rationalp-of-delta-a (nco (- nco 1)) (v0 v0) (dv dv) (g1 g1) (Kt Kt))))))
    (+ (delta-a nco v0 dv g1 Kt)  (delta-a (- nco 1) v0 dv g1 Kt)))

  (define delta-b (nco v0 dv g1 Kt)
    :guard (and (hyp-fn (list :g1 g1 :Kt Kt :v0 v0 :dv dv))
                (integerp nco) (nco-ok (- nco) g1 v0))
    :guard-hints(("Goal"
      :in-theory (disable rationalp-of-m-and-fdco)
      :use(
        (:instance rationalp-of-m-and-fdco (g1 g1) (Kt Kt) (v0 v0) (dv dv) (n nco))) ))
    :returns (d rationalp :hyp :guard)
    (* (expt (gamma Kt) (- nco 1))
       (1- (fdco (m nco v0 g1) v0 dv g1))))


  (define bb (nco-3 v0 dv g1 Kt)
    :guard (and (hyp-fn (list :g1 g1 :Kt Kt :v0 v0 :dv dv))
		(integerp nco-3) (nco-list-ok (list (- -2 nco-3) (+ 2 nco-3)) g1 v0))
    :guard-hints (("Goal" :nonlinearp t))
    :returns (a-sum rationalp :hyp :guard
      :hints(("Goal"
	:nonlinearp t
	:use(
	  (:instance rationalp-of-delta-b (nco (- -2 nco-3)) (v0 v0) (dv dv) (g1 g1) (Kt Kt))
	  (:instance rationalp-of-delta-b (nco (+  2 nco-3))  (v0 v0) (dv dv) (g1 g1) (Kt Kt))))))
    (+ (delta-b (- -2 nco-3) v0 dv g1 Kt) (delta-b (+ nco-3 2) v0 dv g1 Kt)))

;  (local (defthm lemma-2 (implies (rational-listp (list a b c)) (rationalp (+ (* a b) (* a c))))))

  (define delta (nco v0 dv g1 Kt)
    :guard (and (hyp-macro g1 Kt v0 dv) (integerp nco) (<= 3 nco)
		(nco-list-ok (list (- -1 nco) (- nco) (- nco 1) (- 1 nco)) g1 v0))
    :returns (d rationalp :hyp :guard
      :hints(("Goal"
        :use(
	  (:instance lemma-1 (a (expt (gamma Kt) nco))
	                     (b (aa nco v0 dv g1 Kt))
			     (c (bb (- nco 3) v0 dv g1 Kt)))))))
    (* (expt (gamma Kt) nco) (+ (aa nco v0 dv g1 Kt) (bb (- nco 3) v0 dv g1 Kt)))))

;; I suspect that I'll be able to delete delta-orig from this proof by the time I'm done.
;; For now, I'll just prove that delta-orig and delta are equivalent -- we don't even need
;; to use smtlink to show this (but it does take 7.5s on my i5 MBP).
(thm
  (implies (and (hyp-fn (list :v0 v0 :dv dv :g1 g1 :Kt Kt))
		(nco-list-ok (list (1- nco) (1- (- nco))) g1 v0))
	   (equal (delta-orig nco v0 dv g1 Kt)
		  (delta nco v0 dv g1 Kt)))
  :hints(("Goal" :in-theory (enable delta delta-a delta-b aa bb equ-c equ-nc fdco m))))

(encapsulate ()  ; defthm delta-<-0
  ;; The proofs that the "expanded clause implies the original" go through *much*
  ;;   faster without the help from the arithmetic books.
  (disable-theory (theory 'arithmetic-book-only))

  (local (defthm delta-a-bound
    (implies (and (hyp-fn (list :g1 g1 :Kt Kt :v0 v0 :dv dv))
		  (integerp nco) (<= 3 nco) (< nco (1- (/ (mu) (* 2 *beta* g1)))))
	     (< (aa nco v0 dv g1 Kt)
		(* (expt (gamma Kt) (- nco 1)) (* 4 *beta* g1 (/ (1+ (* 2 *alpha* v0))))
		   (+ 1 (gamma Kt)))))
    :hints(("Goal''" :in-theory (enable delta-a aa equ-c equ-nc fdco gamma m mu)
	     :clause-processor
	     (smtlink-custom-config clause (smt-std-hint "delta-a-bound") )))))


  ;; this takes z3 6 minutes on my laptop -- I might break it into a few simpler lemmas.
  (local (defthm delta-b-bound
    (implies (and (hyp-fn (list :g1 g1 :Kt Kt :v0 v0 :dv dv))
		  (integerp nco-3) (<= 0 nco-3) (< nco-3 (- (/ (mu) (* 2 *beta* g1)) 4)))
	     (< (bb nco-3 v0 dv g1 Kt)
		(* (expt (gamma Kt) (- -3 nco-3)) *beta* g1 (/ (mu)) (/ (+ 2 (* *alpha* v0))) -13/16)))
    :hints(("Goal''" :in-theory (enable delta-b bb equ-c equ-nc fdco gamma m mu)
	     :clause-processor
	     (smtlink-custom-config clause (smt-std-hint "delta-b-bound") )))))


  (local (defthm lemma-1  ; the key inequality for showing (< (delta ...)  0)
    (implies (and (hyp-fn (list :g1 g1 :Kt Kt :v0 v0 :dv dv))
		  (integerp nco-3) (<= 0 nco-3) (< nco-3 (- (/ (mu) (* 2 *beta* g1)) 4)))
	     (< (+ (* (expt (gamma Kt) (+ nco-3 2)) (* 4 *beta* g1 (/ (1+ (* 2 *alpha* v0)))) (+ 1 (gamma Kt)))
		   (* (expt (gamma Kt) (- -3 nco-3)) *beta* g1 (/ (mu)) (/ (+ 2 (* *alpha* v0))) -13/16)) 0))
    :hints(("Goal''" :in-theory (enable gamma mu)
	     :clause-processor
	     (smtlink-custom-config clause (smt-std-hint "lemma-1") )))))

  (enable-theory (theory 'arithmetic-book-only))

  (local (defthm lemma-rationalp-of-a-bound ; needed for the main proof
    (implies (and (hyp-fn (list :g1 g1 :Kt Kt :v0 v0)) (integerp nco))
	     (rationalp (+ (* 4 g1 (/ (+ 1 (* 2 v0))) (expt (gamma Kt) nco))
			   (* 4 g1 (/ (+ 1 (* 2 v0))) (expt (gamma Kt) (+ -1 nco))))))
    :hints (("Goal" :in-theory (enable gamma)))))

  (local (defthm lemma-rationalp-of-aa ; the instance of rational-of-aa needed for the main proof
    (implies (and (hyp-fn (list :g1 g1 :Kt Kt :v0 v0 :dv dv))
		  (integerp nco) (< nco (1- (/ (* 2 *beta* g1)))))
	     (rationalp (aa nco v0 dv g1 Kt)))
    :hints (("Goal"
      :nonlinearp t
      :in-theory (disable rationalp-of-aa)
      :use((:instance rationalp-of-aa (nco nco) (v0 v0) (dv dv) (g1 g1) (Kt Kt)))))))

  (local (defthm lemma-rationalp-of-bb ; the instance of rational-of-bb needed for the main proof
    (implies (and (hyp-fn (list :g1 g1 :Kt Kt :v0 v0 :dv dv))
		  (integerp nco) (<= 3 nco) (< nco (1- (/ (* 2 *beta* g1)))))
	     (rationalp (bb (- nco 3) v0 dv g1 Kt)))
    :hints (("Goal"
      :nonlinearp t
      :in-theory (disable rationalp-of-bb)
      :use((:instance rationalp-of-bb (nco-3 (- nco 3)) (v0 v0) (dv dv) (g1 g1) (Kt Kt)))))))

  (local (defthm b-bound-corollary  ; instantiate delta-b-bound with (nco-3 (- nco 3))
    (implies (and (hyp-fn (list :g1 g1 :Kt Kt :v0 v0 :dv dv))
		  (integerp nco) (<= 3 nco) (< nco (- (/ (mu) (* 2 *beta* g1)) 1)))
	     (< (bb (- nco 3) v0 dv g1 Kt)
		(* (expt (gamma Kt) (- nco)) *beta* g1 (/ (mu)) (/ (+ 2 (* *alpha* v0))) -13/16)))
    :hints(("Goal" :in-theory (disable delta-b-bound)
      :use((:instance delta-b-bound (nco-3 (- nco 3)) (v0 v0) (dv dv) (g1 g1) (Kt Kt)))))))

  (local (defthm lemma-1-corollary ; instantiate lemma-1 with (nco-3 (- nco 3))
    (implies (and (hyp-fn (list :g1 g1 :Kt Kt :v0 v0 :dv dv))
		  (integerp nco) (<= 3 nco) (< nco (- (/ (mu) (* 2 *beta* g1)) 1)))
	     (< (+ (* (expt (gamma Kt) (- nco 1)) (* 4 *beta* g1 (/ (1+ (* 2 *alpha* v0)))) (+ 1 (gamma Kt)))
		   (* (expt (gamma Kt) (- nco)) *beta* g1 (/ (mu)) (/ (+ 2 (* *alpha* v0))) -13/16)) 0))
    :hints(("Goal" :in-theory (disable lemma-1)
      :use((:instance lemma-1 (nco-3 (- nco 3)) (v0 v0) (g1 g1) (Kt Kt)))))))

  (local (defthm lemma-2
    (implies (and (hyp-fn (list :g1 g1 :Kt Kt :v0 v0 :dv dv))
		  (integerp nco) (<= 3 nco) (< nco (- (/ (mu) (* 2 *beta* g1)) 1)))
	     (< (+ (aa nco v0 dv g1 Kt) (bb (- nco 3) v0 dv g1 Kt)) 0))
    :hints(("Goal''"
      :clause-processor (smtlink clause
	'(  (:python-file "lemma-3")
	    (:let ( (a0 (aa nco v0 dv g1 Kt) rationalp)
		    (a1 (* (expt (gamma Kt) (- nco 1)) (* 4 *beta* g1 (/ (1+ (* 2 *alpha* v0))))
			   (+ 1 (gamma Kt))) rationalp)
		    (b0 (bb (- nco 3) v0 dv g1 Kt) rationalp)
		    (b1 (* (expt (gamma Kt) (- nco)) *beta* g1 (/ (mu)) (/ (+ 2 (* *alpha* v0)))
			   -13/16) rationalp)))
	    (:hypothesize ((< a0 a1) (< b0 b1) (< (+ a1 b1) 0)))
	    (:use ( (:let  ( (lemma-rationalp-of-aa)
			     (lemma-rationalp-of-a-bound)
			     (lemma-rationalp-of-bb)))
		    (:hypo ( (delta-a-bound) (b-bound-corollary) (lemma-1-corollary))))))
	    )))))

  (defthm delta-<-0
    (implies (and (hyp-fn (list :g1 g1 :Kt Kt :v0 v0 :dv dv))
		  (integerp nco) (<= 3 nco) (< nco (- (/ (mu) (* 2 *beta* g1)) 1)))
	     (< (delta nco v0 dv g1 Kt) 0))
    :hints(
      ("Goal"
	:in-theory (e/d (delta) (lemma-2 expt-gamma-kt-is-positive))
	:use((:instance lemma-2 (nco nco) (v0 v0) (dv dv) (g1 g1) (Kt Kt))))
      ("Subgoal 2"
       :use((:instance expt-gamma-kt-is-positive (n nco) (Kt Kt)))))))

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
	   (Smtlink clause
				'( (:expand ((:function ())
					     (:expansion-level 1)))
				  (:python-file "except-for-delta-smaller-than-0-lemma1")
				  (:let ())
				  (:hypothesize ()))
				)))
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
  (implies (basic-params n 3 v0 dv g1 phi0
                         (< (+ (A n phi0 v0 dv g1)
                               (* (B-expt n)
                                  (B-sum 1 (+ -1 -1 n) v0 dv g1)))
                            0))
           (< (+ (A (+ 1 n) phi0 v0 dv g1)
                 (* (B-expt (+ 1 n))
                    (B-sum 1 (+ -1 n) v0 dv g1))) 0))
  :hints (("Goal"
           :use ((:instance phi-2n+1-<-0-inductive)))))

(defthm phi-2n+1-<-0-base-lemma
  (IMPLIES (AND (RATIONALP V0)
              (RATIONALP PHI0)
              (RATIONALP DV)
              (<= 1 (* 10/9 V0))
              (<= V0 11/10)
              (<= (- (* 8000 DV)) 1)
              (<= (* 8000 DV) 1)
              (<= 0 PHI0)
              (< PHI0
                 (+ -1 (/ (+ 2561/3200 V0))
                    (* DV (/ (+ 2561/3200 V0)))
                    (* V0 (/ (+ 2561/3200 V0))))))
         (< (+ (* 1/3125 PHI0)
               (/ (+ 3201/3200 V0))
               (* 1/125 (/ (+ 1599/1600 V0)))
               (* 1/25 (/ (+ 3199/3200 V0)))
               (* 1/625 (/ (+ 3197/3200 V0)))
               (* DV (/ (+ 3201/3200 V0)))
               (* V0 (/ (+ 3201/3200 V0)))
               (* 1/125 DV (/ (+ 1599/1600 V0)))
               (* 1/125 V0 (/ (+ 1599/1600 V0)))
               (* 1/25 DV (/ (+ 3199/3200 V0)))
               (* 1/25 V0 (/ (+ 3199/3200 V0)))
               (* 1/625 DV (/ (+ 3197/3200 V0)))
               (* 1/625 V0 (/ (+ 3197/3200 V0))))
            656/625))
  :hints (("Goal"
	   :clause-processor
  	   (Smtlink clause
  				'( (:expand ((:function ())
  					     (:expansion-level 1)))
  				  (:python-file "phi-2n+1-smaller-than-0-base")
  				  (:let ())
  				  (:hypothesize ()))
          )))
  )

(defthm phi-2n+1-<-0-base
    (implies (basic-params-equal n 2 v0 dv g1 phi0)
	   (< (phi-2n-1 (1+ n) phi0 v0 dv g1) 0))
  :hints (("Goal"
           :use ((:instance phi-2n+1-<-0-base-lemma))))
  )

(defthm phi-2n+1-<-0-lemma-stupid-lemma1
  (IMPLIES
 (AND
     (IMPLIES
          (AND (AND (INTEGERP N)
                    (RATIONALP G1)
                    (RATIONALP V0)
                    (RATIONALP PHI0)
                    (RATIONALP DV))
               (EQUAL N 2)
               (EQUAL G1 1/3200)
               (<= 9/10 V0)
               (<= V0 11/10)
               (<= -1/8000 DV)
               (<= DV 1/8000)
               (<= 0 PHI0)
               (< PHI0
                  (+ -1
                     (* (FIX (+ 1 (FIX (+ V0 DV))))
                        (/ (+ 1
                              (FIX (* (+ 1
                                         (* (+ (FIX (* (+ 1 (FIX V0)) 1)) -1)
                                            (/ G1))
                                         -640)
                                      G1))))))))
          (< (PHI-2N-1 (+ 1 N) PHI0 V0 DV G1) 0))
     (EQUAL N 2)
     (NOT (OR (NOT (INTEGERP N)) (< N 1)))
     (IMPLIES
          (AND (AND (INTEGERP (+ -1 N))
                    (RATIONALP G1)
                    (RATIONALP V0)
                    (RATIONALP DV)
                    (RATIONALP PHI0))
               (<= 2 (+ -1 N))
               (<= (+ -1 N) 640)
               (EQUAL G1 1/3200)
               (<= 9/10 V0)
               (<= V0 11/10)
               (<= -1/8000 DV)
               (<= DV 1/8000)
               (<= 0 PHI0)
               (< PHI0
                  (+ -1
                     (* (FIX (+ 1 (FIX (+ V0 DV))))
                        (/ (+ 1
                              (FIX (* (+ 1
                                         (* (+ (FIX (* (+ 1 (FIX V0)) 1)) -1)
                                            (/ G1))
                                         -640)
                                      G1))))))))
          (< (+ (A (FIX N) PHI0 V0 DV 1/3200)
                (* (B-EXPT (FIX N))
                   (B-SUM 1 (+ -1 -1 N) V0 DV 1/3200)))
             0))
     (INTEGERP N)
     (RATIONALP G1)
     (RATIONALP V0)
     (RATIONALP DV)
     (RATIONALP PHI0)
     (<= 2 N)
     (<= N 640)
     (EQUAL G1 1/3200)
     (<= 9/10 V0)
     (<= V0 11/10)
     (<= -1/8000 DV)
     (<= DV 1/8000)
     (<= 0 PHI0)
     (< PHI0
        (+ -1
           (* (FIX (+ 1 (FIX (+ V0 DV))))
              (/ (+ 1
                    (FIX (* (+ 1
                               (* (+ (FIX (* (+ 1 (FIX V0)) 1)) -1)
                                  (/ G1))
                               -640)
                            G1))))))))
 (< (+ (A (+ 1 N) PHI0 V0 DV 1/3200)
       (* (B-EXPT (+ 1 N))
          (B-SUM 1 (+ -1 N) V0 DV 1/3200)))
    0)))

(defthm phi-2n+1-<-0-lemma-stupid-lemma2
  (IMPLIES
 (AND
     (IMPLIES
          (AND (AND (INTEGERP N)
                    (RATIONALP G1)
                    (RATIONALP V0)
                    (RATIONALP DV)
                    (RATIONALP PHI0))
               (<= 3 N)
               (<= N 640)
               (EQUAL G1 1/3200)
               (<= 9/10 V0)
               (<= V0 11/10)
               (<= -1/8000 DV)
               (<= DV 1/8000)
               (<= 0 PHI0)
               (< PHI0
                  (+ -1
                     (* (FIX (+ 1 (FIX (+ V0 DV))))
                        (/ (+ 1
                              (FIX (* (+ 1
                                         (* (+ (FIX (* (+ 1 (FIX V0)) 1)) -1)
                                            (/ G1))
                                         -640)
                                      G1)))))))
               (< (+ (A N PHI0 V0 DV G1)
                     (* (B-EXPT N)
                        (B-SUM 1 (+ -1 -1 N) V0 DV G1)))
                  0))
          (< (+ (A (+ 1 N) PHI0 V0 DV G1)
                (* (B-EXPT (+ 1 N))
                   (B-SUM 1 (+ -1 N) V0 DV G1)))
             0))
     (< 2 N)
     (NOT (OR (NOT (INTEGERP N)) (< N 1)))
     (IMPLIES
          (AND (AND (INTEGERP (+ -1 N))
                    (RATIONALP G1)
                    (RATIONALP V0)
                    (RATIONALP DV)
                    (RATIONALP PHI0))
               (<= 2 (+ -1 N))
               (<= (+ -1 N) 640)
               (EQUAL G1 1/3200)
               (<= 9/10 V0)
               (<= V0 11/10)
               (<= -1/8000 DV)
               (<= DV 1/8000)
               (<= 0 PHI0)
               (< PHI0
                  (+ -1
                     (* (FIX (+ 1 (FIX (+ V0 DV))))
                        (/ (+ 1
                              (FIX (* (+ 1
                                         (* (+ (FIX (* (+ 1 (FIX V0)) 1)) -1)
                                            (/ G1))
                                         -640)
                                      G1))))))))
          (< (+ (A (FIX N) PHI0 V0 DV 1/3200)
                (* (B-EXPT (FIX N))
                   (B-SUM 1 (+ -1 -1 N) V0 DV 1/3200)))
             0))
     (INTEGERP N)
     (RATIONALP G1)
     (RATIONALP V0)
     (RATIONALP DV)
     (RATIONALP PHI0)
     (<= 2 N)
     (<= N 640)
     (EQUAL G1 1/3200)
     (<= 9/10 V0)
     (<= V0 11/10)
     (<= -1/8000 DV)
     (<= DV 1/8000)
     (<= 0 PHI0)
     (< PHI0
        (+ -1
           (* (FIX (+ 1 (FIX (+ V0 DV))))
              (/ (+ 1
                    (FIX (* (+ 1
                               (* (+ (FIX (* (+ 1 (FIX V0)) 1)) -1)
                                  (/ G1))
                               -640)
                            G1))))))))
 (< (+ (A (+ 1 N) PHI0 V0 DV 1/3200)
       (* (B-EXPT (+ 1 N))
          (B-SUM 1 (+ -1 N) V0 DV 1/3200)))
    0)))

(defthm phi-2n+1-<-0-lemma
  (IMPLIES (basic-params n 2 v0 dv g1 phi0)
           (< (+ (A (+ 1 n) phi0 V0 DV 1/3200)
                 (* (B-EXPT (+ 1 N))
                    (B-SUM 1 (+ -1 N) V0 DV 1/3200)))
              0))
  :hints (("Goal"
           :do-not '(simplify)
           :in-theory (disable B-expt)
           :induct (B-sum 1 N V0 DV 1/3200)
           )
          ("Subgoal *1/2"
           :cases ((< n 2) (equal n 2) (> n 2)))
          ("Subgoal *1/2.2"
           :use ((:instance phi-2n+1-<-0-base)
                 (:instance phi-2n+1-<-0-lemma-stupid-lemma1)))
          ("Subgoal *1/2.1"
           :use ((:instance phi-2n+1-<-0-inductive-corollary)
                 (:instance phi-2n+1-<-0-lemma-stupid-lemma2)))
          ))

(defthm phi-2n+1-<-0
  (implies (basic-params n 2 v0 dv g1 phi0)
	   (< (phi-2n-1 (1+ n) phi0 v0 dv g1) 0))
  :hints (("Goal"
           :use ((:instance phi-2n+1-<-0-lemma))))
  )

(defthm phi-2n-1-<-0
  (implies (basic-params n 3 v0 dv g1 phi0)
	   (< (phi-2n-1 n phi0 v0 dv g1) 0))
  :hints (("Goal"
	   :use ((:instance phi-2n+1-<-0
			    (n (1- n)))))))
)

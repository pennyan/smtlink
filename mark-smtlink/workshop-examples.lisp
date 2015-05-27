;; This file contains all examples appearing in the
;; workshop paper.
(in-package "ACL2")

(include-book "arithmetic/top" :dir :system)
(add-include-book-dir :cp "/ubc/cs/home/y/yanpeng/project/ACL2/smtlink")
(include-book "top" :dir :cp)
(tshell-ensure)

;; need the configurable trust tag
;;(defttag :Smtlink-custom-config)
;; configurations
(local
 (progn
   (defun my-smtlink-config ()
     (declare (xargs :guard t))
     (make-smtlink-config :dir-interface
			  "/ubc/cs/home/y/yanpeng/project/ACL2/smtlink/z3\_interface"
			  :dir-files
			  "z3\_files"
			  :SMT-module
			  "ACL22SMT"
			  :SMT-class
			  "to_smt"
			  :smt-cmd
			  "python"
			  :dir-expanded
			  "expanded"))
   (defattach smt-cnf my-smtlink-config)))


;; 2.1 A simple example
(defthm A-simple-example
  (implies (and (and (rationalp x)
                     (rationalp y))
                (and (>= x 2)
                     (<= y -2)))
           (>= (+ (* x x) (* y y)) 4))
  :hints (("Goal"
           :clause-processor
           (Smtlink-custom-config clause
                                  '()
                                  state)
           ))
  )

;; 2.2 User defined functions
(defun udf-func (x y) (+ (* x x) (* y y)))

(defthm User-defined-functions
  (implies (and (and (rationalp x)
                     (rationalp y))
                (and (>= x 2)
                     (<= y -2)))
           (>=  (udf-func x y) 4))
  :hints (("Goal"
           :clause-processor
           (Smtlink-custom-config clause
                                  '((:expand ((:functions ((udf-func rationalp)))
                                               (:expansion-levels 1)))
                                    )
                                  state)
           ))
  )


;; function expansion example
(defun fac (n)
  (if (or (<= n 0) (not (integerp n)))
      1
    (* n (fac (1- n)))))

(defthm test-lemma (implies  (and
                             (IMPLIES
                              (IF
                               (INTEGERP N)
                               (IF (EQUAL |var4| (FAC (BINARY-+ '-1 |var3|)))
                                   (NOT (< '2 N))
                                   'NIL)
                               'NIL)
                              (INTEGERP |var4|))
                            
                             (IMPLIES
                              (IF (INTEGERP N) (NOT (< '2 N)) 'NIL)
                              (<
                               ((LAMBDA
                                 (|var0|)
                                 (IF
                                  (IF (NOT (< '0 |var0|))
                                      (NOT (< '0 |var0|))
                                      (NOT (INTEGERP |var0|)))
                                  '1
                                  (BINARY-*
                                   |var0|
                                   ((LAMBDA
                                     (|var1|)
                                     (IF
                                      (IF (NOT (< '0 |var1|))
                                          (NOT (< '0 |var1|))
                                          (NOT (INTEGERP |var1|)))
                                      '1
                                      (BINARY-*
                                       |var1|
                                       ((LAMBDA
                                         (|var2|)
                                         (IF
                                          (IF (NOT (< '0 |var2|))
                                              (NOT (< '0 |var2|))
                                              (NOT (INTEGERP |var2|)))
                                          '1
                                          (BINARY-*
                                           |var2|
                                           ((LAMBDA
                                             (|var3|)
                                             (IF
                                              (IF (NOT (< '0 |var3|))
                                                  (NOT (< '0 |var3|))
                                                  (NOT (INTEGERP |var3|)))
                                              '1
                                              (BINARY-*
                                               |var3|
                                               (FAC (BINARY-+ '-1 |var3|)))))
                                            (BINARY-+ '-1 |var2|)))))
                                        (BINARY-+ '-1 |var1|)))))
                                    (BINARY-+ '-1 |var0|)))))
                                N)
                               '10)))
                            (IMPLIES (IF (INTEGERP N) (NOT (< '2 N)) 'NIL)
                                     (< (FAC N) '10))))

(defthm fac-thm
  (implies (and (and (integerp n))
                (and (<= n 2)))
           (< (fac n) 10))
  :hints
  (("Goal"
    :clause-processor
    (Smtlink-custom-config clause
             '((:expand ((:functions ((fac integerp)))
                         (:expansion-level 4)))
               (:use ((:main (test-lemma)))))
             state)))
  )

;; 2.3 User supplied substitutions and hypothesis
(defthm User-supplied-substitution-&-hypothesis
    (implies (and (and (rationalp a)
                       (rationalp b)
                       (rationalp gamma)
                       (integerp m)
                       (integerp n))
                  (and (> gamma 0)
                       (< gamma 1)
                       (> m 0)
                       (< m n)))
             (>= (* (expt gamma m) (- (* (+ a b) (+ a b)) (* 2 a b)))
                 (* (expt gamma n) (* 2 a b))))
  :hints
  (("Goal"
    :clause-processor
    (Smtlink-custom-config clause
	     '((:let ((expt_gamma_m (expt gamma m) rationalp)
		      (expt_gamma_n (expt gamma n) rationalp)))
	       (:hypothesize ((< expt_gamma_n expt_gamma_m)
			      (> expt_gamma_m 0)
			      (> expt_gamma_n 0)))
	       )
	     state))))


;; 2.4 Nested hints
;; See Section 2.2 User defined functions under function expansion

;; 2.5 Uinterpreted functions
(local
 (progn
   (defun my-smtlink-expt-config ()
     (declare (xargs :guard t))
     (change-smtlink-config *default-smtlink-config*
			  :SMT-module
			  "RewriteExpt"
			  :SMT-class
			  "to_smt_w_expt"
        ))
   (defattach smt-cnf my-smtlink-expt-config)))

(defthm Uninterpreted-function
  (implies (and (and (rationalp x)
                     (integerp n))
                (and (> x 0)))
           (> (expt x n) 0))
  :hints
  (("Goal"
    :clause-processor
    (Smtlink-custom-config clause
             '((:uninterpreted-functions ((expt rationalp integerp rationalp))))
             state)))
  )


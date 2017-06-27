;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software


(in-package "SMT")
(include-book "../top")

;; (include-book "clause-processors/meta-extract-user" :dir :system)
(include-book "centaur/misc/tshell" :dir :system)
;; (include-book "misc/eval" :dir :system)

(deftheory before-arith (current-theory :here))
(include-book "arithmetic-5/top" :dir :system)
(deftheory after-arith (current-theory :here))
(deftheory arithmetic-book-only (set-difference-theories (theory 'after-arith) (theory 'before-arith)))

(defsection examples
  :parents (tutorial)

  (defttag :tshell)
  (value-triple (tshell-ensure))

  (defun my-smtlink-expt-config ()
    (declare (xargs :guard t))
    (make-smtlink-config :interface-dir "/Users/penny/Work/fun/theorem_proving/smtlink/z3_interface"
                         :SMT-files-dir "z3\_files"
                         :SMT-module    "RewriteExpt"
                         :SMT-class     "to_smt_w_expt"
                         :SMT-cmd       "python"
                         :file-format   ".py"))

  (defun my-smtlink-hint ()
    (declare (xargs :guard t))
    (change-smtlink-hint
     *default-smtlink-hint*
     :functions (list (make-func :name 'expt))
     :rm-file nil
     :smt-params nil
     :smt-cnf (my-smtlink-expt-config)))

  (defattach smt-hint my-smtlink-hint)

  (add-default-hints '((SMT::SMT-process-hint clause)))

  ;; Section 2. A short tour
  ;; Example 1
  (defun x^2-y^2 (x y) (- (* x x) (* y y)))
  (defthm poly-ineq-example
    (implies (and (real/rationalp x) (real/rationalp y)
                  (<= (+ (* (/ 9 8) x x) (* y y)) 1)
                  (<=  (x^2-y^2 x y) 1))
             (<= y (* 3 (- x (/ 17 8)) (- x (/ 17 8)))))
    :hints(("Goal"
            :clause-processor
            (SMT::Smtlink clause nil))))

  ;; Example 2
  (defun ||x^2+y^2||^2 (x y) (+ (* x x) (* y y)))
  (defthm poly-of-expt-example
    (implies (and (real/rationalp x) (real/rationalp y) (real/rationalp z)
                  (integerp m) (integerp n)
                  (< 0 z) (< z 1) (< 0 m) (< m n))
             (<= (* 2 (expt z n) x y)
                 (* (expt z m) (||x^2+y^2||^2 x y))))
    :hints (("Goal"
             :clause-processor
             (SMT::Smtlink clause
                           (:functions ((expt :formals ((r rationalp)
                                                        (i rationalp))
                                              :returns ((ex rationalp))
                                              :level 0))
                                       :hypotheses (((< (expt z n) (expt z m)))
                                                    ((< 0 (expt z m)))
                                                    ((< 0 (expt z n))))
                                       :main-hint nil
                                       :smt-fname ""
                                       :int-to-rat t
                                       :rm-file nil
                                       :smt-solver-params nil
                                       :smt-solver-cnf nil)))))

  ;; Buggy example
  (acl2::must-fail
   (defthm non-theorem
     (implies (and (real/rationalp x)
                   (real/rationalp y)
                   (integerp (/ x y)))
              (not (equal y 0)))
     :hints(("Goal"
             :clause-processor
             (SMT::Smtlink clause nil)))
     :rule-classes nil)
   )
  )

;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software


(in-package "SMT")
(include-book "../top")
(include-book "centaur/sv/tutorial/support" :dir :system)

(value-triple (tshell-ensure))
(add-default-hints '((SMT::SMT-process-hint clause)))

;; Section 2. A short tour
;; Example 1
(def-saved-event x^2-y^2
  (defun x^2-y^2 (x y) (- (* x x) (* y y))))

(def-saved-event poly-ineq
  (defthm poly-ineq-example
    (implies (and (real/rationalp x) (real/rationalp y)
                  (<= (+ (* (/ 9 8) x x) (* y y)) 1)
                  (<=  (x^2-y^2 x y) 1))
             (<= y (* 3 (- x (/ 17 8)) (- x (/ 17 8)))))
    :hints(("Goal"
            :smtlink nil)))
  )

(deftutorial Example-1
  :parents (Tutorial)
  :short "Example 1: the basics"
  :long "<h3>Example 1</h3>
<p>The first example is a basic polynomial inequality.  Let's say we want to
prove below theorem:</p>
<box><p><b><color rgb='#323cbe'>Theorem 1.</color></b> Let @($ x\\in
R$) and @($ y \\in R$), @(\forall x\\in R\ and\exists y\\in R,\\ if\\
  \\frac{9x^2}{8}+y^2 <= 1\\ and\\ x^2+y^2 <= 1,\\ then\\
  y<=3(x-\\frac{17}{8})^2)
         @(`(:code ($ x^2-y^2))`)
         @(`(:code ($ poly-ineq))`) </p></box>")

(def-saved-event smtconf-expt-tutorial
  (defun my-smtlink-expt-config ()
    (declare (xargs :guard t))
    (change-smtlink-config *default-smtlink-config*
                           :interface-dir "../z3_interface"
                           :smt-module    "RewriteExpt"
                           :smt-class     "to_smt_w_expt"
                           :smt-cmd       "python"
                           :pythonpath    "")))

(def-saved-event smtconf-expt-defattach-tutorial
  (defattach custom-smt-cnf my-smtlink-expt-config))

;; Example 2
(def-saved-event ||x^2+y^2||^2
  (defun ||x^2+y^2||^2 (x y) (+ (* x x) (* y y))))

(def-saved-event poly-of-expt-example
  (encapsulate ()
    (local (include-book "arithmetic-5/top" :dir :system))
    (defthm poly-of-expt-example
      (implies (and (real/rationalp x) (real/rationalp y) (real/rationalp z)
                    (integerp m) (integerp n)
                    (< 0 z) (< z 1) (< 0 m) (< m n))
               (<= (* 2 (expt z n) x y)
                   (* (expt z m) (||x^2+y^2||^2 x y))))
      :hints (("Goal"
               :smtlink-custom (:functions ((expt :formals ((r rationalp)
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
                                :smt-solver-params nil))))))
(deftutorial Example-2
  :parents (Tutorial)
  :short "Example 2"
  :long "<h3>Example 2</h3>
         @(`(:code ($ smtconf-expt-tutorial))`)
         @(`(:code ($ smtconf-expt-defattach-tutorial))`)
         @(`(:code ($ ||x^2+y^2||^2))`)
         @(`(:code ($ poly-of-expt-example))`)")

;; Buggy example
(def-saved-event non-theorem-example
  (acl2::must-fail
   (defthm non-theorem
     (implies (and (real/rationalp x)
                   (real/rationalp y)
                   (integerp (/ x y)))
              (not (equal y 0)))
     :hints(("Goal"
             :smtlink nil))
     :rule-classes nil)))

(deftutorial Example-3
  :parents (Tutorial)
  :short "Example 3"
  :long "<h3>Example 3</h3>
         @(`(:code ($ non-theorem-example))`)")


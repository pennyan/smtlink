;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software


(in-package "SMT")
(include-book "../top")
(include-book "centaur/sv/tutorial/support" :dir :system)
(include-book "arithmetic-5/top" :dir :system)

(value-triple (tshell-ensure))
(sv::def-saved-event add-hints-tutorial
                     (add-default-hints '((SMT::SMT-process-hint clause))))

(sv::def-saved-event smtconf-tutorial
                     (defun my-smtlink-config ()
                       (declare (xargs :guard t))
                       (change-smtlink-config *default-smtlink-config*
                                              :interface-dir "../z3_interface/"
                                              :SMT-files-dir ""
                                              :SMT-module "ACL2_to_Z3"
                                              :SMT-class "ACL22SMT"
                                              :SMT-cmd "python"
                                              :file-format ".py")))

(sv::def-saved-event smthint-tutorial
                     (defun my-smtlink-hint ()
                       (declare (xargs :guard t))
                       (change-smtlink-hint *default-smtlink-hint*
                                            :smt-cnf (my-smtlink-config))))

(sv::def-saved-event smthint-attach-1-tutorial
                     (defattach smt-hint my-smtlink-hint))

;; Section 2. A short tour
;; Example 1
(sv::def-saved-event x^2-y^2
  (defun x^2-y^2 (x y) (- (* x x) (* y y))))

(sv::def-saved-event poly-ineq-example
  (defthm poly-ineq-example
    (implies (and (real/rationalp x) (real/rationalp y)
                  (<= (+ (* (/ 9 8) x x) (* y y)) 1)
                  (<=  (x^2-y^2 x y) 1))
             (<= y (* 3 (- x (/ 17 8)) (- x (/ 17 8)))))
    :hints(("Goal"
            :smtlink nil)))
)

(sv::deftutorial Example-1
                 :parents (Tutorial)
                 :short "Example 1"
                 :long "<h3>Example 1</h3>
                        @(`(:code ($ poly-ineq-example))`)")

(sv::def-saved-event smtconf-expt-tutorial
                     (defun my-smtlink-expt-config ()
                       (declare (xargs :guard t))
                       (change-smtlink-config *default-smtlink-config*
                                              :interface-dir "../z3_interface"
                                              :SMT-files-dir ""
                                              :SMT-module    "RewriteExpt"
                                              :SMT-class     "to_smt_w_expt"
                                              :SMT-cmd       "python"
                                              :file-format   ".py")))

(sv::def-saved-event smthint-expt-tutorial
                     (defun my-smtlink-hint-expt ()
                       (declare (xargs :guard t))
                       (change-smtlink-hint *default-smtlink-hint*
                                            :smt-cnf (my-smtlink-expt-config))))

(sv::def-saved-event smthint-attach-2-tutorial
                     (defattach smt-hint my-smtlink-hint-expt))

;; Example 2
(sv::def-saved-event ||x^2+y^2||^2
  (defun ||x^2+y^2||^2 (x y) (+ (* x x) (* y y))))

(sv::def-saved-event poly-of-expt-example
  (defthm poly-of-expt-example
    (implies (and (real/rationalp x) (real/rationalp y) (real/rationalp z)
                  (integerp m) (integerp n)
                  (< 0 z) (< z 1) (< 0 m) (< m n))
             (<= (* 2 (expt z n) x y)
                 (* (expt z m) (||x^2+y^2||^2 x y))))
    :hints (("Goal"
             :smtlink (:functions ((expt :formals ((r rationalp)
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

(sv::deftutorial Example-2
                 :parents (Tutorial)
                 :short "Example 2"
                 :long "<h3>Example 2</h3>
                        @(`(:code ($ smtconf-expt-tutorial))`)")

;; Buggy example
(sv::def-saved-event non-theorem-example
(acl2::must-fail
 (defthm non-theorem
   (implies (and (real/rationalp x)
                 (real/rationalp y)
                 (integerp (/ x y)))
            (not (equal y 0)))
   :hints(("Goal"
           :smtlink nil))
   :rule-classes nil)))

(sv::deftutorial Example-3
                 :parents (Tutorial)
                 :short "Example 3"
                 :long "<h3>Example 3</h3>
                        @(`(:code ($ non-theorem-example))`)")



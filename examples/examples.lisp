;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software


(in-package "ACL2")
(include-book "../top")
(in-package "SMT")
(include-book "clause-processors/meta-extract-user" :dir :system)


(defun ||x^2+y^2||^2 (x y) (+ (* x x) (* y y)))

(defun my-smtlink-hint ()
  (declare (xargs :guard t))
  (change-smtlink-hint
   *default-smtlink-hint*
   :functions (list (make-func :name 'X^2+Y^2^2
                               :formals (list (make-decl :name 'x
                                                         :type (make-hint-pair :thm 'rationalp :hints nil))
                                              (make-decl :name 'y
                                                         :type (make-hint-pair :thm 'rationalp :hints nil)))
                               :returns (list (make-decl :name 'x
                                                         :type (make-hint-pair :thm 'rationalp :hints nil)))
                               :body '(binary-+ (binary-* x x) (binary-* y y))
                               :expansion-depth 1
                               :uninterpreted nil))
   :smt-hint '(:clause-processor (SMT-trusted-cp clause))))

(defattach smt-hint my-smtlink-hint)

(add-default-hints '((SMT::SMT-hint-wrapper-hint clause)))

;; Section 2. A short tour
;; Example 1
(defthm poly-ineq-example
  (implies (and (rationalp x) (rationalp y)
                (<= (+ (* (/ 9 8) x x) (* y y)) 1)
                (<= (- (* x x) (* y y)) 1))
           (<= y (* 3 (- x (/ 17 8)) (- x (/ 17 8)))))
    :hints(("Goal"
            :clause-processor
            (SMT::Smtlink clause))))

;; Example 2
(defthm poly-of-expt-exlsample
  (implies (and (rationalp x) (rationalp y) (rationalp z)
                (integerp m) (integerp n)
                (< 0 z) (< z 1) (< 0 m) (< m n))
           (<= (* 2 (expt z n) x y)
               (* (expt z m) (||x^2+y^2||^2 x y))))
  :hints (("Goal"
           :clause-processor
           (SMT::Smtlink clause))))

;; ;; Buggy example
;; (defthm non-theorem
;;   (implies (and (rationalp x)
;;                 (rationalp y)
;;                 (integerp (/ x y)))
;;            (not (equal y 0)))
;;        :hints(("Goal" :clause-processor (Smtlink clause nil))))

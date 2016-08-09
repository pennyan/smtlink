;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software


(in-package "ACL2")
(include-book "../top")

(add-default-hints '((SMT-hint-wrapper-hint clause)))

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

;; ;; Example 2
;; (defun ||x^2+y^2||^2 (x y) (+ (* x x) (* y y)))
;; (defthm poly-of-expt-example
;;   (implies (and (rationalp x) (rationalp y) (rationalp z)
;;                 (integerp m) (integerp n)
;;                 (< 0 z) (< z 1) (< 0 m) (< m n))
;;            (<= (* 2 (expt z n) x y)
;;                (* (expt z m) (||x^2+y^2||^2 x y))))
;;   :hints (("Goal"
;;            :clause-processor
;;            (Smtlink-custom-config clause
;;                                   '((:expand ((:functions ((||x^2+y^2||^2 rationalp)))
;;                                               (:expansion-level 1)))
;;                                     (:let ((expt_z_m (expt z m) rationalp)
;;                                            (expt_z_n (expt z n) rationalp)))
;;                                     (:hypothesize ((< expt_z_n expt_z_m)
;;                                                    (< 0 expt_z_m)
;;                                                    (< 0 expt_z_n))))))))

;; ;; Buggy example
;; (defthm non-theorem
;;   (implies (and (rationalp x)
;;                 (rationalp y)
;;                 (integerp (/ x y)))
;;            (not (equal y 0)))
;;        :hints(("Goal" :clause-processor (Smtlink clause nil))))

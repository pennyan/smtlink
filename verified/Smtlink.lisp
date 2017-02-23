;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software
;;

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)

;; (include-book "SMT-hint-interface")

;; ;; --------------------------------------------------------

;; ;; Example:
;; ;; (defthm ...
;; ;;   ...
;; ;;   :hints (("Goal"
;; ;;            :clause-processor
;; ;;            (SMT::smtlink clause
;; ;;                          :hints (:functions ()
;; ;;                                  :hypotheses
;; ;;                                  :main-hint )))))

;; (define smtlink-hint-syntax-p ((hint-lst listp))
;;   :returns (syntax-good? booleanp)
;;   (or t hint-lst))

;; (define process-hint ((hint smtlink-hint-syntax-p) (smt-hint smtlink-hint-p))
;;   :returns (returned-smt-hint smtlink-hint-p)
;;   :irrelevant-formals-ok t
;;   :ignore-ok t
;;   smt-hint)

;; (defmacro Smtlink (clause hint)
;;   (b* ((combined-hint (process-hint hint (smt-hint))))
;;     `(Smtlink-subgoals ,clause
;;                        ;; A and G-prim and hints
;;                        (Smt-goal-generator ,clause ,new-hint state))))


(defmacro Smtlink (clause)
  `(Smtlink-subgoals ,clause
                     ;; A and G-prim and hints
                     (Smt-goal-generator ,clause (smt-hint) state)))

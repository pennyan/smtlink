;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software
;;

;;
;; ABSTRACTED VERIFIED CLAUSE PROCESSOR FOR SMTLINK
;;
;;   This verified clause processor decomposes the main goal
;;    into three subgoals. The clause processor is verified
;;    meaning it's proven that the three subgoals imply the
;;    original main clause. This is verified in theorem:
;;      "correctness-of-Smtlink-subgoals"
;;
;;   This higher order way of write proofs in ACL2 requires
;;     treating goals as program expressions (meaning they
;;     are quoted terms). Proving theorems on expressions
;;     instead of programs requires an evaluator that tells
;;     the theorem the ``meaning'' of the expressions.
;;

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)

;; Define identity function
(defun SMT-please (x)
  (declare (ignore x)
           (xargs :guard t))
  t)

(defthm hint-wrapper-forward
; Probably not needed when tau-system is active.
  (implies (not (SMT-please x))
           nil)
  :rule-classes :forward-chaining)

(in-theory (disable (:d SMT-please)
                    (:e SMT-please)
                    (:t SMT-please)))


;;
;; Explanation for clause decomposition
;;
;; A -> G-prim
;; A \and G-prim -> G
;; A \or G
;;
;; A : The auxiliary hypothesis clauses
;; G-prim : The expanded original clause
;; G : The original clause

(defun Smtlink-subgoals (cl clause)
  (b* ((A (car clause))
       (G-prim (cadr clause))
       (hints (caddr clause))
       (G (disjoin cl))

       (cl0 `((not ,A) (not (SMT-please ',hints)) ,G-prim))
       (cl1 `((not ,A) (not ,G-prim) ,G))
       (cl2 `(,A ,G)))
    `(,cl0 ,cl1 ,cl2)))

(defevaluator ev-Smtlink-subgoals ev-lst-Smtlink-subgoals
  ((not x) (if x y z) (SMT-please x)))

(local (in-theory (disable nth)))

(defthm correctness-of-Smtlink-subgoals
  (implies (and (pseudo-term-listp cl)
                (alistp b)
                (ev-Smtlink-subgoals
                 (conjoin-clauses (Smtlink-subgoals cl clauses))
                 b))
           (ev-Smtlink-subgoals (disjoin cl) b))
  :rule-classes :clause-processor)

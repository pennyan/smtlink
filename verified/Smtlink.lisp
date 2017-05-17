;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software
;;

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)

(include-book "SMT-hint-interface")
(include-book "SMT-verified-cps")

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

(define smtlink-hint-syntax-p ((hint-lst t))
  :returns (syntax-good? booleanp)
  :ignore-ok t
  (if (listp hint-lst) t nil))

(define smtlink-hint-syntax-fix ((hint-lst smtlink-hint-syntax-p))
  :returns (fixed-syntax smtlink-hint-syntax-p)
  :ignore-ok t
  :irrelevant-formals-ok t
  (if (smtlink-hint-syntax-p hint-lst) hint-lst nil))

(define combine-hints ((user-hints smtlink-hint-syntax-p) (hint smtlink-hint-p))
  :returns (combined-hint smtlink-hint-p)
  :ignore-ok t
  (b* ((user-hints (smtlink-hint-syntax-fix user-hints))
       (hint (smtlink-hint-fix hint)))
    hint))

  (define process-hint ((cl pseudo-term-listp) (user-hint t))
    :returns (subgoal-lst pseudo-term-list-listp)
    :enabled t
    (b* ((cl (pseudo-term-list-fix cl))
         (- (cw "cl: ~q0" cl))
         ((unless (smtlink-hint-syntax-p user-hint)) (list cl))
;;         (user-hint (smtlink-hint-syntax-fix user-hint))
         (combined-hint (combine-hints user-hint (smt-hint)))
         (cp-hint `(:clause-processor (Smt-verified-cp clause ',combined-hint)))
         (subgoal-lst (cons `(hint-please ',cp-hint 'process-hint) cl)))
      (list subgoal-lst)))

  ;; ------------------------------------------------------------
  ;;         Prove correctness of clause processor
  ;;

;; -----------------------------------------------------------------
;;       Define evaluators

(defevaluator ev-process-hint ev-lst-process-hint
  ((not x) (if x y z) (hint-please hint tag)))

(def-join-thms ev-process-hint)

  (defthm correctness-of-process-hint
    (implies (and (pseudo-term-listp cl)
                  (alistp b)
                  (ev-process-hint
                   (conjoin-clauses (process-hint cl hint))
                   b))
             (ev-process-hint (disjoin cl) b))
    :rule-classes :clause-processor)

;; Smtlink is a macro that generates a clause processor hint. This clause
;;   processor hint generates a clause, with which a new smt-hint is attached.
;;   This new smt-hint combines user given hints with defattach hints.
;; A computed hint will be waiting to take the clause and hint for clause
;;   expansion and transformation.
(defmacro Smtlink (clause hint)
  `(process-hint ,clause ,hint))

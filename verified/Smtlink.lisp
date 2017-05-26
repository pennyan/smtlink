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

;; (defsection Smtlink-process-user-hint
;;   :parents (Smtlink)
;;   :short "Functionalities for processing user hints given to Smtlink. User
;;   hints will be merged with (smt-hint)."

  ;; --------------------------------------------------------

  ;; Example:
  ;; (defthm ...
  ;;   ...
  ;;   :hints (("Goal"
  ;;            :clause-processor
  ;;            (SMT::smtlink clause
  ;;                          '(:functions ()
  ;;                            :hypotheses ()
  ;;                            :main-hint ()
  ;;                            :int-to-rat nil
  ;;                            :smt-fname ""
  ;;                            :rm-file t
  ;;                            :smt-solver-params ()
  ;;                            :smt-cnf ())))))

  (define true-list-fix ((lst t))
    :short "Fixing function for true-listp."
    :returns (fixed-lst true-listp)
    (if (true-listp lst)
        lst
      nil))

  (defconst *syntax-lst*
    '((:functions . listp)
      (:hypotheses . listp)
      (:main-hint . listp)
      (:int-to-rat . booleanp)
      (:smt-fname . stringp)
      (:rm-file . booleanp)
      (:smt-solver-params . listp)
      (:smt-cnf . listp)))

  (define eval-type ((type symbolp) (content t))
    :short "Evaluate if a content is of the given type."
    :returns (type-correct? booleanp)
    (cond ((equal type 'booleanp) (booleanp content))
          ((equal type 'stringp) (stringp content))
          ((equal type 'listp) (listp content))
          (t (symbolp content))))

  (define check-syntax ((hint-lst true-listp) (used true-listp))
    :short "Main function for checking the syntax of a Smtlink hint list."
    :returns (syntax-good? booleanp)
    :hints (("Goal" :in-theory (enable true-list-fix)))
    (b* ((hint-lst (true-list-fix hint-lst))
         ((if (endp hint-lst)) t)
         ((cons first rest) hint-lst)
         ((cons second rest-of-second) rest)
         ((if (member-equal first used))
          (er hard? 'Smtlink=>check-syntax "Already defined ~p0.~%" first))
         (exist? (assoc-equal first *syntax-lst*))
         ((unless exist?) nil)
         (type (cdr exist?))
         (type-correct? (eval-type type second))
         ((unless type-correct?) nil))
      (check-syntax rest-of-second (cons first used))))

  (define smtlink-hint-syntax-p ((hint-lst t))
    :short "Syntax check for Smtlink hint."
    :returns (syntax-good? booleanp)
    (b* (;; hint-lst should be a listp
         ((unless (true-listp hint-lst)) nil)
         ;; hint-lst should not exceed a length of 16 elements
         ((unless (<= (len hint-lst) 16)) nil))
      (check-syntax hint-lst nil)))

  (define smtlink-hint-syntax-fix ((hint-lst smtlink-hint-syntax-p))
    :short "Fixing function for Smtlink hint syntax."
    :returns (fixed-syntax smtlink-hint-syntax-p)
    :ignore-ok t
    :irrelevant-formals-ok t
    (if (smtlink-hint-syntax-p hint-lst) hint-lst nil))

  (define combine-hints ((raw-user-hints smtlink-hint-syntax-p)
                         (hint smtlink-hint-p))
    :returns (combined-hint smtlink-hint-p)
    :ignore-ok t
    (b* ((user-hints (smtlink-hint-syntax-fix raw-user-hints))
         (- (cw "Warning (Smtlink=>combine-hints): Smtlink hint syntax
    violated~% ~q0Therefore user provided Smtlink hint ignored.~%" raw-user-hints))
         (hint (smtlink-hint-fix hint)))
      hint))

  (define process-hint ((cl pseudo-term-listp) (user-hint t))
    :returns (subgoal-lst pseudo-term-list-listp)
    :enabled t
    (b* ((cl (pseudo-term-list-fix cl))
         ((unless (smtlink-hint-syntax-p user-hint)) (list cl))
         (- (cw "user-hint: ~q0" user-hint))
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
;;  )

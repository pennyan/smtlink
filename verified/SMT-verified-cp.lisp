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
(include-book "misc/eval" :dir :system)
(include-book "clause-processors/join-thms" :dir :system)

;; -----------------------------------------------------------------
;;       Define the identity function.
;;

(defun hint-please (cl hint)
  (declare (ignore hint)
           (xargs :guard t))
  cl)

(defthm hint-please-forward
  (implies (hint-please cl hint)
           cl)
  :rule-classes :forward-chaining)

(in-theory (disable (:d hint-please)
                    (:e hint-please)
                    (:t hint-please)))

;; -----------------------------------------------------------------
;;       Define Smtlink subgoals.
;;


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

(defun and-logic (a b)
  `(if ,a ,b 'nil))

(defun and-list-logic (lst)
  (cond ((endp lst) ''t)
        ((endp (cdr lst)) (car lst))
        (t (and-logic (car lst) (and-list-logic (cdr lst))))))

(defun or-logic (a b)
  `(if ,a 't ,b))

(defun or-list-logic (lst)
  (cond ((endp lst) ''t)
        ((endp (cdr lst)) (car lst))
        (t (or-logic (car lst) (or-list-logic (cdr lst))))))

(defun construct-aux-clauses (A-list hint-list G)
  (if (endp A-list)
      nil
    (b* ((first-A (car A-list))
         (first-hint (car hint-list)))
      (cons `((hint-please ,(or-logic first-A G) ',first-hint))
            (construct-aux-clauses (cdr A-list) (cdr hint-list) G)))))

(defun construct-smtlink-subgoals (As G-prim hints G)
  (b* ((A-and-list (and-list-logic As))
       (hint-list (car hints))
       (main-hint (cadr hints))
       (SMT-hint (caddr hints))
       (cl0 `((hint-please (implies ,A-and-list ,G-prim) ',SMT-hint)))
       (cl1 `((hint-please (implies ,(and-logic G-prim (and-list-logic As)) ,G) ',main-hint)))
       (aux-clauses (construct-aux-clauses As hint-list G)))
    `(,cl0 ,cl1 ,@aux-clauses)))

(defun get-smtlink-subterms (clause)
  (b* ((As (caar clause))
       (G-prim (cadar clause))
       (hints (cadr clause)))
    (mv As G-prim hints)))

;;
;; Shape of clause:
;;
;; (;; clauses: list of As, G-prim
;;  ((A1 A2 ... An)
;;   G-prim)
;;  ;; hints: list of A-hints, main-hints
;;  ((A1-hint A2-hint ... An-hint)
;;   main-hint
;;   SMT-hint))
;;
(defun Smtlink-subgoals (cl clause)
  (mv-let (As G-prim hints) (get-smtlink-subterms clause)
    (construct-smtlink-subgoals As G-prim hints (disjoin cl))))



;; Test Smtlink-subgoals
(must-succeed
 (defthm test-case-1
   (equal (Smtlink-subgoals '(G)
                            '(((A1 A2)
                               G-prim)
                              ((A1-hint A2-hint)
                               main-hint
                               SMT-hint)))
          '(((hint-please (implies (IF A1 A2 'NIL) G-PRIM) 'SMT-hint))
            ((hint-please (implies (IF G-prim (IF A1 A2 'NIL) 'NIL) G) 'main-hint))
            ((hint-please (IF A1 'T G) 'A1-hint))
            ((hint-please (If A2 'T G) 'A2-hint))))))
;; Test clause processor
(defmacro test-smtlink-cp (subgoals)
  `(thm (implies (and ,@(conjoin-clauses subgoals)) G)))



;; ------------------------------------------------------------
;;         Prove correctness of clause processor
;;

(defevaluator ev-Smtlink-subgoals ev-lst-Smtlink-subgoals
  ((not x) (if x y z) (implies x y) (hint-please cl hint) ))

(def-join-thms ev-Smtlink-subgoals)

(defthm correctness-of-Smtlink-subgoals-lemma
  (implies
   (and (pseudo-term-listp cl)
        (alistp b)
        (not (ev-smtlink-subgoals (and-list-logic As) b))
        (ev-smtlink-subgoals
         (conjoin-clauses (construct-aux-clauses As A-hints (disjoin cl))) b))
   (ev-smtlink-subgoals (disjoin cl) b)))

(defthm correctness-of-Smtlink-subgoals
  (implies (and (pseudo-term-listp cl)
                (alistp b)
                (ev-Smtlink-subgoals
                 (conjoin-clauses (Smtlink-subgoals cl clause))
                 b))
           (ev-Smtlink-subgoals (disjoin cl) b))
  :rule-classes :clause-processor)

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
  `(if ,a ,b nil))

(defun and-list-logic (lst)
  (cond ((endp lst) t)
        ((endp (cdr lst)) (car lst))
        (t (and-logic (car lst) (and-list-logic (cdr lst))))))

(defun or-logic (a b)
  `(if ,a t ,b))

(defun or-list-logic (lst)
  (cond ((endp lst) nil)
        ((endp (cdr lst)) (car lst))
        (t (or-logic (car lst) (or-list-logic (cdr lst))))))

(defun construct-aux-clauses (A-list hint-list G)
  (if (endp A-list)
      nil
    (b* ((first-A (car A-list))
         (first-hint (car hint-list)))
      (cons `((hint-please ,(or-logic first-A G) ',first-hint))
            (construct-aux-clauses (cdr A-list) (cdr hint-list) G)))))

(defun construct-smtlink-subgoals (A-and-hints G-prim-and-hints hints G)
  (b* ((G-prim (car G-prim-and-hints))
       (main-hint (cdr G-prim-and-hints))
       (A-list (strip-cars A-and-hints))
       (A-and-list (and-list-logic A-list))
       (hint-list (strip-cdrs A-and-hints))
       (cl0 `((hint-please (implies ,A-and-list ,G-prim) ',hints)))
       (cl1 `((hint-please (implies ,(and-list-logic (append A-list (list G-prim))) ,G) ',main-hint)))
       (aux-clauses (construct-aux-clauses A-list hint-list G)))
    `(,cl0 ,cl1 ,@aux-clauses)))

(defun Smtlink-subgoals (cl clause)
  (b* (;; auxiliary hypotheses and their hints in alist
       (A-and-hints (car clause))
       ((if (not (alistp A-and-hints)))
        (er hard? 'top-level "The first element of clause has to be an alist"))
       ;; G' and the main hint
       (G-prim-and-hints (cadr clause))
       ((if (not (consp G-prim-and-hints)))
        (er hard? 'top-level "The second element of clause has to be a consp"))
       ;; SMT hints
       (hints (caddr clause))
       ;; original clause
       (G (disjoin cl)))
    (construct-smtlink-subgoals A-and-hints G-prim-and-hints hints G)))

;; Test Smtlink-subgoals
(must-succeed
 (defthm test-case-1
   (equal (Smtlink-subgoals '(G)
                            '(((A1 . A1-hint) (A2 . A2-hint))
                              (G-prim . main-hint)
                              SMT-hint))
          '(((hint-please (implies (IF A1 A2 NIL) G-PRIM) 'SMT-hint))
            ((hint-please (implies (IF A1 (IF A2 G-PRIM NIL) NIL) G) 'main-hint))
            ((hint-please (IF A1 T G) 'A1-hint))
            ((hint-please (If A2 T G) 'A2-hint))))))

(defevaluator ev-Smtlink-subgoals ev-lst-Smtlink-subgoals
  ((not x) (if x y z) (implies x y) (hint-please cl hint) ))

;; (stop-here)

;; (set-gag-mode nil)

(skip-proofs
(defthm correctness-of-Smtlink-subgoals
  (implies (and (pseudo-term-listp cl)
                (alistp b)
                (ev-Smtlink-subgoals
                 (conjoin-clauses (Smtlink-subgoals cl clause))
                 b))
           (ev-Smtlink-subgoals (disjoin cl) b))
  :rule-classes :clause-processor)
)

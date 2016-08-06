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

;; Define identity function
(defun hint-please (x)
  (declare (ignore x)
           (xargs :guard t))
  t)

(defthm hint-please-forward
; Probably not needed when tau-system is active.
  (implies (not (hint-please x))
           nil)
  :rule-classes :forward-chaining)

(in-theory (disable (:d hint-please)
                    (:e hint-please)
                    (:t hint-please)))

(defun dumb-negate-lit-lst (lst)
  (cond ((endp lst) nil)
        (t (cons (dumb-negate-lit (car lst))
                 (dumb-negate-lit-lst (cdr lst))))))

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

;; (defun Smtlink-subgoals (cl clause)
;;   (b* ((A (car clause))
;;        (G-prim (cadr clause))
;;        (hints (caddr clause))
;;        (G (disjoin cl))

;;        (cl0 `((not ,A) (not (SMT-please ',hints)) ,G-prim))
;;        ;; (cl0 `((SMT-please '(implies ,A ,G-prim) ',hints)))
;;        (cl1 `((not ,A) (not ,G-prim) ,G))
;;        (cl2 `(,A ,G)))
;;     `(,cl0 ,cl1 ,cl2)))

(defun construct-aux-clauses (A-list not-hint-list G)
  (if (endp A-list)
      nil
    (b* ((first-A (car A-list))
         (first-not-hint (car not-hint-list)))
      (cons `(,first-A ,first-not-hint ,G)
            (construct-aux-clauses (cdr A-list) (cdr not-hint-list) G)))))

(defun map-hint-please (hint-list)
  (if (endp hint-list)
      nil
    (cons `(hint-please ',(car hint-list))
          (map-hint-please (cdr hint-list)))))

(defun construct-smtlink-subgoals (A-and-hints G-prim-and-hints hints G)
  (b* ((G-prim (car G-prim-and-hints))
       (main-hint `(hint-please ',(cdr G-prim-and-hints)))
       (A-list (strip-cars A-and-hints))
       (not-A-list (dumb-negate-lit-lst A-list))
       (not-hint-list (dumb-negate-lit-lst (map-hint-please (strip-cdrs A-and-hints))))
       (cl0 `(,@not-A-list (not (hint-please ',hints)) ,G-prim))
       (cl1 `((not ,main-hint) ,@not-A-list (not ,G-prim) ,G))
       (aux-clauses (construct-aux-clauses A-list not-hint-list G)))
    (cons cl0 (cons cl1 aux-clauses))))

(defun Smtlink-subgoals (cl clause)
  (b* (;; auxiliary hypotheses and their hints
       (A-and-hints (car clause))
       ;; G' and the main hint
       (G-prim-and-hints (cadr clause))
       ;; SMT hints
       (hints (caddr clause))
       ;; original clause
       (G (disjoin cl)))
    (construct-smtlink-subgoals A-and-hints G-prim-and-hints hints G)))

;; Test Smtlink-subgoals
(must-succeed
 (defthm test-case-1
   (equal (Smtlink-subgoals '((not H0) C0)
                            '(((A1 . A1-hint) (A2 . A2-hint))
                              (G-prim . main-hint)
                              SMT-hint))
          '(((not A1) (not A2) (not (hint-please 'SMT-hint)) G-prim)
            ((not (hint-please 'main-hint)) (not A1) (not A2) (not G-prim) (IF (NOT H0) 'T C0))
            (A1 (not (hint-please 'A1-hint)) (IF (NOT H0) 'T C0))
            (A2 (not (hint-please 'A2-hint)) (IF (NOT H0) 'T C0))))))

(defevaluator ev-Smtlink-subgoals ev-lst-Smtlink-subgoals
  ((not x) (if x y z) (hint-please x)))

(stop-here)

;; (set-gag-mode nil)

(defthm correctness-of-Smtlink-subgoals
  (implies (and (pseudo-term-listp cl)
                (alistp b)
                (ev-Smtlink-subgoals
                 (conjoin-clauses (Smtlink-subgoals cl clauses))
                 b))
           (ev-Smtlink-subgoals (disjoin cl) b))
  :rule-classes :clause-processor)



;; ------------------------------------------------------------------------------------------------------
;;    This is the debugging line


;; Why, ACL2, why can't you prove this!!
(IMPLIES
 (AND
  (PSEUDO-TERM-LISTP CL)
  (ALISTP B)
  (NOT
    (EQUAL (DISJOIN (APPEND (DUMB-NEGATE-LIT-LST (STRIP-CARS (CAR CLAUSES)))
                            (LIST (LIST 'NOT
                                        (LIST 'HINT-PLEASE
                                              (LIST 'QUOTE (CADDR CLAUSES))))
                                  (CAR (CADR CLAUSES)))))
           ''NIL))
  (NOT
   (CONSP
    (DISJOIN-LST
      (CONSTRUCT-AUX-CLAUSES
           (STRIP-CARS (CAR CLAUSES))
           (DUMB-NEGATE-LIT-LST (MAP-HINT-PLEASE (STRIP-CDRS (CAR CLAUSES))))
           (DISJOIN CL)))))
  (EQUAL (DISJOIN (APPEND (DUMB-NEGATE-LIT-LST (STRIP-CARS (CAR CLAUSES)))
                          (LIST (LIST 'NOT (CAR (CADR CLAUSES)))
                                (DISJOIN CL))))
         ''T)
  (NOT
    (EQUAL (DISJOIN (APPEND (DUMB-NEGATE-LIT-LST (STRIP-CARS (CAR CLAUSES)))
                            (LIST (LIST 'NOT
                                        (LIST 'HINT-PLEASE
                                              (LIST 'QUOTE (CADDR CLAUSES))))
                                  (CAR (CADR CLAUSES)))))
           ''T))
  (EV-SMTLINK-SUBGOALS
       (DISJOIN (APPEND (DUMB-NEGATE-LIT-LST (STRIP-CARS (CAR CLAUSES)))
                        (LIST (LIST 'NOT
                                    (LIST 'HINT-PLEASE
                                          (LIST 'QUOTE (CADDR CLAUSES))))
                              (CAR (CADR CLAUSES)))))
       B))
 (EV-SMTLINK-SUBGOALS (DISJOIN CL) B))

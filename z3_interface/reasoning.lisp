;; Copyright (C) 2015, University of British Columbia
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software
;;
;; This file contains reasoning for how proofs work in RewriteExpt.py
;; Yan Peng, UBC, 17th Nov 2016
;;

;; Here goes the reasoning for why it is ok just to add 
;; (implies (and H0 H1 H2 ... ) C)
;; => (or (not H0) (not H1) (not H2) ... C)

;; Need Z3 to prove:
;; unsat of (Not (or (not H0) (not H1) (not H2) ... C))

;; Now we want to prove:
;; (implies (and H0 H1 H2 ... ) P1)
;; I.e. want Z3 to prove
;; unsat of (Not (or (not H0) (not H1) (not H2) ... P1))
;; which is equivalent to
;; (Not (or (not H0) (not H1) (not H2))) and (Not P1)
;; which is equivalent to
;; (H0 and H1 and ...) and (Not P1)

;; So the old version is correct!

;; Now let,
;; A = (H0 and H1 and ...)
;; B = (Not P1)

;; our new A is not (H0 and H1 and ...) but rather
;; (implies (H0 and H1 and ...) C)

;; If we go through the same logic, suppose we want to prove:
;; (implies (implies (and H0 H1 H2 ... ) C) P1)
;; which is equivalent to
;; (implies (or (not H0) (not H1) (not H2) ... C) P1)
;; which is equivalent to
;; (or (not (or (not H0) (not H1) (not H2) ... C)) P1)
;; which is equivalent to
;; (or (and H0 H1 H2 ... (not C)) P1)

;; I.e. want Z3 to prove
;; unsat of (Not (or (and H0 H1 H2 ... (not C)) P1))
;; which is equivalent to
;; (not (and H0 H1 H2 ... (not C))) and (not P1)
;; which is equivalent to
;; (or (not H0) (not H1) (not H2) ... C) and (not P1)

;; The reasoning is checked in ACL2

(in-package "ACL2")
;;
;; Here are the ACL2 theorems to check.
;; Note this is not a formal proof because it's only got three H's.
;; But it should be easy to develop an induction proof that's
;; automatically checkable by ACL2.
;;
(defthm implication-equivalence
  (implies (boolean-listp '(H1 H2 H3 C P1))
           (equal (implies (implies (and H1 H2 H3) C) P1)
                  (or (and H1 H2 H3 (not C)) P1)) )
  :rule-classes nil)

(defthm unsat-theorem-equivalence
 (implies (boolean-listp '(H1 H2 H3 C P1))
          (equal (not (or (and H1 H2 H3 (not C)) P1))
                 (and (or (not H1) (not H2) (not H3) C) (not P1))))
 :rule-classes nil)

(defthm irrelevant-conclusion
  (implies (boolean-listp '(H1 H2 H3 C P1))
           (implies (implies (implies (and H1 H2 H3) C) P1)
                    (implies (and H1 H2 H3) P1)))
  :rule-classes nil)

;; Above reasoning means that if we can prove
;;   (implies (implies (and H1 H2 H3) C) P1)
;; by demonstrating unsat of
;;   (and (or (not H1) (not H2) (not H3) C) (not P1))
;; we can then conclude (implies (and H1 H2 H3) P1).
;; But if we failed to prove:
;;   (implies (implies (and H1 H2 H3) C) P1)
;; we can't conclude anything.
;; However, it is possible to fail the proof of:
;;   (implies (implies (and H1 H2 H3) C) P1)
;; Since this is a stronger proof.

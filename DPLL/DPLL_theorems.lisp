;; There are two files for the proof of recurrence model of the 
;; DPLL: global.lisp, DPLL_functions.lisp and DPLL_theorems.lisp.

;; DPLL_theorems.lisp 
;; DPLL_theorems.lisp defines and proves the theorems and lemmas
;; needed in this proof.
(in-package "ACL2")
(include-book "arithmetic/top-with-meta" :dir :system)

; Include global constants
(local (include-book "global"))
; Include summation
(local (include-book "summation"))
; Include DPLL functions
(local (include-book "DPLL_functions"))

;; ------------------------------------------------------------
;; Proof for the upper half
;; Prove equivalence of the summing formula and the recurrence
; For C
(defthm eqv-sum-rec-C
  (implies (and (integerp m)
                (<= m (- (/ (equ-c) *g1*) 3))
                (>= m (- (/ (equ-c) *g1*) 320))
                (rationalp p0)
                (>= p0 0)
                (<= p0 (- (/ (* (mu) (+ 1 (* *alpha* *v0*))) (+ 1 (* *beta* (+ m 1) *g1*))) 1))
                (integerp j)
                (>= j 1))
           (equal (state-j-sum-C m j) (state-j-rec-C m j))))
; For P
(skip-proofs
(defthm eqv-sum-rec-P
  (implies (and (integerp m)
                (<= m (- (/ (equ-c) *g1*) 3))
                (>= m (- (/ (equ-c) *g1*) 320))
                (rationalp p0)
                (>= p0 0)
                (<= p0 (- (/ (* (mu) (+ 1 (* *alpha* *v0*))) (+ 1 (* *beta* (+ m 1) *g1*))) 1))
                (integerp j)
                (>= j 1))
           (equal (state-j-sum-P p0 m j) (state-j-rec-P p0 m j)))
  :rule-classes nil)
)
; Prove the equivalence of peeling off the first two terms
(defthm peel-first-2-terms-sum-p
  (implies (and (integerp m)
                (<= m (- (/ (equ-c) *g1*) 3))
                (>= m (- (/ (equ-c) *g1*) 320))
                (integerp j)
                (> j 0))
           (equal (sum-p 0 j (list m j))
                  (+ (f-term 0 (list m j)) (f-term 1 (list m j)) (sum-p 2 j (list m j)))))
  :hints (("Goal"
           :expand ((:free (x) (hide x)))
           :use ((:functional-instance
                  (:instance peel-first-2-terms (args (list m j)))
                  (f (lambda (x args) (f-term x args)))
                  (summation sum-p)))
           :do-not-induct t
           :in-theory (disable peel-first-2-terms reverse-the-sum))))
(defthm peel-first-2-terms-p
  (implies (and (integerp j)
                (> j 1)
                (integerp m)
                (<= m (- (/ (equ-c) *g1*) 3))
                (>= m (- (/ (equ-c) *g1*) 320)))
           (equal (state-j-sum-P p0 m j)
                  (+ (* (Expt (gamma) j) p0) (+ (f-term 0 (list m (- j 1))) (f-term 1 (list m (- j 1))) (sum-p 2 (- j 1) (list m (- j 1)))))))
  :hints (("Goal"
           :use ((:instance peel-first-2-terms-sum-p)))))
(defthm peel-first-2-terms-p-assc
  (implies (and (integerp j)
                (> j 1)
                (integerp m)
                (<= m (- (/ (equ-c) *g1*) 3))
                (>= m (- (/ (equ-c) *g1*) 320)))
           (equal (state-j-sum-P p0 m j)
                  (+ (* (Expt (gamma) j) p0) (f-term 0 (list m (- j 1))) (f-term 1 (list m (- j 1))) (sum-p 2 (- j 1) (list m (- j 1)))))))

(defthm 2n-1-peel-first-2-terms-lemma1
  (implies (and (integerp m)
                (integerp j)
                (<= m (- (/ (equ-c) *g1*) 3))
                (>= m (- (/ (equ-c) *g1*) 320))
                (equal j (- (* 2 (n m)) 1)))
           (> j 1)))
  

(defthm 2n-1-peel-first-2-terms-lemma2
  (implies (and (integerp m)
                (integerp j)
                (<= m (- (/ (equ-c) *g1*) 3))
                (>= m (- (/ (equ-c) *g1*) 320))
                (equal j (- (* 2 (n m)) 1)))
           (implies (> j 1)
                    (equal (state-j-sum-P p0 m j)
                           (+ (* (Expt (gamma) j) p0)
                              (f-term 0 (list m (- j 1)))
                              (f-term 1 (list m (- j 1)))
                              (sum-p 2 (- j 1) (list m (- j 1)))))))
  :hints (("Goal"
           :use ((:instance peel-first-2-terms-p-assc)))))

(defthm 2n-1-peel-first-2-terms-lemma3
  (implies (and (integerp m)
                (integerp j)
                (<= m (- (/ (equ-c) *g1*) 3))
                (>= m (- (/ (equ-c) *g1*) 320))
                (equal j (- (* 2 (n m)) 1)))
           (and (> j 1)
                (implies (> j 1)
                    (equal (state-j-sum-P p0 m j)
                           (+ (* (Expt (gamma) j) p0)
                              (f-term 0 (list m (- j 1)))
                              (f-term 1 (list m (- j 1)))
                              (sum-p 2 (- j 1) (list m (- j 1))))))))
  :hints (("Goal"
           :use ((:instance 2n-1-peel-first-2-terms-lemma1)
                 (:instance 2n-1-peel-first-2-terms-lemma2)))))

(defthm 2n-1-peel-first-2-terms-lemma4
  (implies (and (integerp m)
                (<= m (- (/ (equ-c) *g1*) 3))
                (>= m (- (/ (equ-c) *g1*) 320))
                (integerp j)
                (equal j (- (* 2 (n m)) 1)))
           (equal (state-j-sum-P p0 m j)
                  (+ (* (Expt (gamma) j) p0)
                     (f-term 0 (list m (- j 1)))
                     (f-term 1 (list m (- j 1)))
                     (sum-p 2 (- j 1) (list m (- j 1))))))
  :hints (("Goal" 
           :in-theory (theory 'minimal-theory)
           :use ((:instance 2n-1-peel-first-2-terms-lemma3)))))

(defthm 2n-1-peel-first-2-terms-lemma5
  (implies (and (integerp m)
                (<= m (- (/ (equ-c) *g1*) 3))
                (>= m (- (/ (equ-c) *g1*) 320)))
           (equal (state-j-sum-P p0 m (- (* 2 (n m)) 1))
                  (+ (* (Expt (gamma) (- (* 2 (n m)) 1)) p0)
                     (f-term 0 (list m (- (- (* 2 (n m)) 1) 1)))
                     (f-term 1 (list m (- (- (* 2 (n m)) 1) 1)))
                     (sum-p 2 (- (- (* 2 (n m)) 1) 1) (list m (- (- (* 2 (n m)) 1) 1))))))
  :hints (("Goal"
           :use ((:instance 2n-1-peel-first-2-terms-lemma4
                  (j (- (* 2 (n m)) 1)))))))

(defthm 2n-1-peel-first-2-terms-lemma6
  (equal (p-2n-1 p0 m)
         (state-j-sum-P p0 m (- (* 2 (n m)) 1)))
  :hints (("Goal"
           :do-not-induct t)))

(defthm 2n-1-peel-first-2-terms-lemma7
  (equal (- (- (* 2 (n m)) 1) 1)
         (- (* 2 (n m)) 2))
  :hints (("Goal"
           :do-not-induct t)))

(defthm p-2n-1-peel-first-2-terms
  (implies (and (integerp m)
                (<= m (- (/ (equ-c) *g1*) 3))
                (>= m (- (/ (equ-c) *g1*) 320)))
           (equal (p-2n-1 p0 m)
                  (+ (* (Expt (gamma) (- (* 2 (n m)) 1)) p0)
                     (f-term 0 (list m (- (* 2 (n m)) 2)))
                     (f-term 1 (list m (- (* 2 (n m)) 2)))
                     (sum-p 2 (- (* 2 (n m)) 2) (list m (- (* 2 (n m)) 2))))))
  :hints (("Goal"
           :in-theory (theory 'minimal-theory)
           :use ((:instance 2n-1-peel-first-2-terms-lemma5)
                 (:instance 2n-1-peel-first-2-terms-lemma6)
                 (:instance 2n-1-peel-first-2-terms-lemma7)))))

(verbose-pstack nil)
(verbose-pstack t)

(accumulated-persistence nil)
(accumulated-persistence t) 

; Prove a sum can be represent as the first half plus the middle value plus the second half
(defthm divide-in-the-middle-sum-p-lemma1
  (implies (and (integerp m)
                (<= m (- (/ (equ-c) *g1*) 3))
                (>= m (- (/ (equ-c) *g1*) 320)))
           (integerp (n m)))
  :rule-classes :type-prescription)

(defthm divide-in-the-middle-sum-p-lemma2
  (implies (and (integerp m)
                (<= m (- (/ (equ-c) *g1*) 3))
                (>= m (- (/ (equ-c) *g1*) 320)))
           (and (>= (n m) 3) (<= (n m) 320))))

(defthm divide-in-the-middle-sum-p
  (implies (and (integerp m)
                (<= m (- (/ (equ-c) *g1*) 3))
                (>= m (- (/ (equ-c) *g1*) 320)))
           (equal (sum-p 2 (- (* 2 (n m)) 2) args)
                  (+ (sum-p 2 (- (n m) 1) args) (f-term (n m) args) (sum-p (+ (n m) 1) (- (* 2 (n m)) 2) args))))
  :hints (("Goal"
           :in-theory (theory 'minimal-theory)
           :use ((:instance divide-in-the-middle-sum-p-lemma1)
                 (:instance divide-in-the-middle-sum-p-lemma2)
                 (:functional-instance
                  (:instance divide-in-the-middle (lo 2) (hi (- (* 2 (n m)) 2)) (mid (n m)))
                  (f (lambda (x args) (f-term x args)))
                  (summation sum-p))))))                      ; This proof takes 11mins. Very strange!

(defthm divide-in-the-middle-p
  (implies (and (integerp m)
                (<= m (- (/ (equ-c) *g1*) 3))
                (>= m (- (/ (equ-c) *g1*) 320)))
           (equal (p-2n-1 p0 m)
                  (+ (* (Expt (gamma) (- (* 2 (n m)) 1)) p0)
                     (f-term 0 (list m (- (* 2 (n m)) 2)))
                     (f-term 1 (list m (- (* 2 (n m)) 2)))
                     (+ (sum-p 2 (- (n m) 1) (list m (- (* 2 (n m)) 2))) 
                        (f-term (n m) (list m (- (* 2 (n m)) 2))) 
                        (sum-p (+ (n m) 1) (- (* 2 (n m)) 2) (list m (- (* 2 (n m)) 2)))))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (theory 'minimal-theory)
           :use ((:instance divide-in-the-middle-sum-p (args (list m (- (* 2 (n m)) 2))))
                 (:instance p-2n-1-peel-first-2-terms)))))

(defthm divide-in-the-middle-lemma1
  (equal (f-term (n m) (list m (- (* 2 (n m)) 2))) 0))

(defthm divide-in-the-middle-lemma2
  (implies (and (integerp m)
                (<= m (- (/ (equ-c) *g1*) 3))
                (>= m (- (/ (equ-c) *g1*) 320)))
           (equal (p-2n-1 p0 m)
                  (+ (* (Expt (gamma) (- (* 2 (n m)) 1)) p0)
                     (f-term 0 (list m (- (* 2 (n m)) 2)))
                     (f-term 1 (list m (- (* 2 (n m)) 2)))
                     (+ (sum-p 2 (- (n m) 1) (list m (- (* 2 (n m)) 2)))
                        (sum-p (+ (n m) 1) (- (* 2 (n m)) 2) (list m (- (* 2 (n m)) 2)))))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (theory 'minimal-theory)
           :use ((:instance divide-in-the-middle-p)
                 (:instance divide-in-the-middle-lemma1)))))

; Prove the first sum-p in divide-in-the-middle-lemma2 is equal to 
; a sum by shifting to left by 1
(defthm left-shift-sum-p-1 
  (implies (and (integerp m)
                (<= m (- (/ (equ-c) *g1*) 3))
                (>= m (- (/ (equ-c) *g1*) 320)))
           (equal (sum-p 2 (- (n m) 1) (list m (- (* 2 (n m)) 2)))
                  (sum-p-1 1 (- (n m) 2) 1 (list m (- (* 2 (n m)) 2)))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:functional-instance
                  (:instance left-shift-the-sum (lo 2) (hi (- (n m) 1)) (k 1) (args (list m (- (* 2 (n m)) 2))))
                  (f (lambda (x args) (f-term x args)))
                  (summation sum-p)
                  (summation1 sum-p-1))))))

; Prove the second sum-p in divide-in-the-middle-lemma2 is equal to
; a sum that's reversed and then left shift by n+1
(defthm reverse-and-left-shift-sum-p-2-lemma1
  (implies (and (integerp m)
                (<= m (- (/ (equ-c) *g1*) 3))
                (>= m (- (/ (equ-c) *g1*) 320)))
           (equal (+ 3198 (- m)) (+ 3198 m (- (* 2 m))))))

(defthm reverse-and-left-shift-sum-p-2-a
  (implies (and (integerp m)
                (<= m (- (/ (equ-c) *g1*) 3))
                (>= m (- (/ (equ-c) *g1*) 320)))
           (equal (sum-p (+ (n m) 1) (- (* 2 (n m)) 2) (list m (- (* 2 (n m)) 2)))
                  (sum-p-1 1 (- (n m) 2) (n m) (list m (- (* 2 (n m)) 2)))))
  :hints (("Goal"
           :use ((:instance reverse-and-left-shift-sum-p-2-lemma1)
                 (:functional-instance
                  (:instance left-shift-the-sum (lo (+ (n m) 1)) (hi (- (* 2 (n m)) 2)) (k (n m)) (args (list m (- (* 2 (n m)) 2))))
                  (f (lambda (x args) (f-term x args)))
                  (summation sum-p)
                  (summation1 sum-p-1)))
           :in-theory (disable reverse-and-left-shift-sum-p-2-lemma1))))

(defthm reverse-and-left-shift-sum-p-2-b
  (implies (and (integerp m)
                (<= m (- (/ (equ-c) *g1*) 3))
                (>= m (- (/ (equ-c) *g1*) 320)))
           (equal (sum-p (+ (n m) 1) (- (* 2 (n m)) 2) (list m (- (* 2 (n m)) 2)))
                  (sum-p-3 1 (- (n m) 2) (n m) (list m (- (* 2 (n m)) 2)))))
  :hints (("Goal"
           :use ((:functional-instance
                  (:instance reverse-the-sum-and-left-shift (lo (+ (n m) 1)) (hi (- (* 2 (n m)) 2)) (k (n m)) (args (list m (- (* 2 (n m)) 2))))
                  (f (lambda (x args) (f-term x args)))
                  (summation sum-p)
                  (summation3 sum-p-3))))))

; Prove the sum of the two sum-p is equal to a new sum of summing up
; corresponding terms in the two sums. 
(defthm equal-sum-p-full
  (implies (and (integerp m)
                (<= m (- (/ (equ-c) *g1*) 3))
                (>= m (- (/ (equ-c) *g1*) 320)))
           (equal (p-2n-1 p0 m)
                  (+ (* (Expt (gamma) (- (* 2 (n m)) 1)) p0)
                     (f-term 0 (list m (- (* 2 (n m)) 2)))
                     (f-term 1 (list m (- (* 2 (n m)) 2)))
                     (+ (sum-p-1 1 (- (n m) 2) 1 (list m (- (* 2 (n m)) 2)))
                        (sum-p-3 1 (- (n m) 2) (n m) (list m (- (* 2 (n m)) 2)))))))
  :hints (("Goal"
           :in-theory (theory 'minimal-theory)
           :use ((:instance divide-in-the-middle-lemma2)
                 (:instance left-shift-sum-p-1)
                 (:instance reverse-and-left-shift-sum-p-2-b)))))

; Prove sum-p-3 equals its correspondent sum-p-4
(defthm sum-p-3-as-sum-p-4-lemma1
  (implies (and (integerp m)
                (<= m (- (/ (equ-c) *g1*) 3))
                (>= m (- (/ (equ-c) *g1*) 320)))
           (and (integerp (n m))
                (integerp (+ (n m) 1))
                (integerp (- (* 2 (n m)) 2))))
  :rule-classes :type-prescription)

(defthm sum-p-3-as-sum-p-4-lemma2
  (implies (and (integerp m)
                (<= m (- (/ (equ-c) *g1*) 3))
                (>= m (- (/ (equ-c) *g1*) 320)))
           (and (equal (+ (+ (n m) 1) (- (n m))) 1)
                (equal (+ (+ -2 (* 2 (n m))) (- (n m))) (- (n m) 2))
                (equal (+ (+ (n m) 1)
                          (+ -2 (* 2 (n m)))
                          (- (n m))
                          (- (n m)))
                       (- (n m) 1)))))

(defthm sum-p-3-as-sum-p-4
  (implies (and (integerp m)
                (<= m (- (/ (equ-c) *g1*) 3))
                (>= m (- (/ (equ-c) *g1*) 320)))
           (equal (sum-p-4 1 (- (n m) 2) (- (n m) 1) (n m) (list m (- (* 2 (n m)) 2)))
                  (sum-p-3 1 (- (n m) 2) (n m) (list m (- (* 2 (n m)) 2)))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance sum-p-3-as-sum-p-4-lemma1)
                 (:instance sum-p-3-as-sum-p-4-lemma2)
                 (:functional-instance
                  (:instance equivalence-summation3-summation4 
                   (lo (+ (n m) 1)) 
                   (hi (- (* 2 (n m)) 2)) 
                   (k (n m)) 
                   (args (list m (- (* 2 (n m)) 2))))
                  (f (lambda (x args) (f-term x args)))
                  (summation4 sum-p-4)
                  (summation3 sum-p-3)))
           :in-theory (disable reverse-and-left-shift-sum-p-2-lemma1))))

(verbose-pstack nil)
(accumulated-persistence nil)

; Prove the p-2n-1 is equal to a sum using sum-p-full
(defthm p-2n-1-transforming-sum-lemma2
  (implies (and (integerp i)
                (integerp j)
                (integerp k1))
           (equal (+ (sum-p-1 i j k1 args)
                     (sum-p-4 i j x k2 args))
                  (sum-p-full i j x k1 k2 args)))
  :hints (("Goal"
           :induct (sum-p-full i j x k1 k2 args))))

(defthm p-2n-1-transforming-sum-lemma1
  (implies (and (integerp m)
                (<= m (- (/ (equ-c) *g1*) 3))
                (>= m (- (/ (equ-c) *g1*) 320)))
           (equal (+ (sum-p-1 1 (- (n m) 2) 1 (list m (- (* 2 (n m)) 2)))
                     (sum-p-4 1 (- (n m) 2) (- (n m) 1) (n m) (list m (- (* 2 (n m)) 2))))
                  (sum-p-full 1 (- (n m) 2) (- (n m) 1) 1 (n m) (list m (- (* 2 (n m)) 2)))))
  :hints (("Goal"
           :use ((:instance p-2n-1-transforming-sum-lemma2
                  (i 1)
                  (j (- (n m) 2))
                  (k1 1)
                  (k2 (n m))
                  (x (- (n m) 1))
                  (args (list m (- (* 2 (n m)) 2))))))))

(defthm p-2n-1-transforming-sum
  (implies (and (integerp m)
                (<= m (- (/ (equ-c) *g1*) 3))
                (>= m (- (/ (equ-c) *g1*) 320)))
           (equal (p-2n-1 p0 m)
                  (+ (* (Expt (gamma) (- (* 2 (n m)) 1)) p0)
                     (f-term 0 (list m (- (* 2 (n m)) 2)))
                     (f-term 1 (list m (- (* 2 (n m)) 2)))
                     (sum-p-full 1 (- (n m) 2) (- (n m) 1) 1 (n m) (list m (- (* 2 (n m)) 2))))))
  :hints (("Goal"
           :in-theory (theory 'minimal-theory)
           :use ((:instance equal-sum-p-full)
                 (:instance sum-p-3-as-sum-p-4)
                 (:instance p-2n-1-transforming-sum-lemma1)))))

;; -------------------------------------------------------------------
;; This part proves the induction proof developed in the documentation
;;      for the upper half

; Base case
(defthm DPLL-upper-base
  (implies (and (integerp m)
                (equal m (- (/ (equ-c) *g1*) 3))
                (rationalp p0)
                (>= p0 0)
                (<= p0 (- (/ (* (mu) (+ 1 (* *alpha* *v0*))) (+ 1 (* *beta* (+ m 1) *g1*))) 1)))
           (< (p-2n-1 p0 m) 0))
  :rule-classes nil)#|ACL2s-ToDo-Line|#

; Induction case

(defthm B-smaller-than-0-lemma1
  (show-me (implies (and (integerp m)
                (<= m (- (/ (equ-c) *g1*) 3))
                (>= m (- (/ (equ-c) *g1*) 320)))
           (< (+ (f-term (+ 1 (- (n m) 2)) args)
                 (f-term (+ (- (- (n m) 1) (- (n m) 2)) (n m)) args)) 0))))

(defthm B-smaller-than-0
  (implies (and (integerp m)
                (<= m (- (/ (equ-c) *g1*) 3))
                (>= m (- (/ (equ-c) *g1*) 320)))
           (< (sum-p-full 1 (- (n m) 2) (- (n m) 1) 1 (n m) (list m (- (* 2 (n m)) 2))) 0))
  :hints (("Goal"
           :induct (sum-p-full i j x k1 k2 args))))

;; -------------------------------------------------------------------
;; This part proves the induction proof developed in the documentation
;;      for the lower half

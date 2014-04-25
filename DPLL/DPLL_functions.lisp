;; There are two files for the proof of recurrence model of the 
;; DPLL: global.lisp, DPLL_functions.lisp and DPLL_theorems.lisp.

;; DPLL_functions.lisp 
;; DPLL_functions.lisp defines functions needed, including the
;; recurrence, the equilibrium point and so on.

(in-package "ACL2")

; Include global constants
(local (include-book "global"))
; Include theorems for summations
(local (include-book "summation"))
; Define intermediate variables
(defun equ-c ()
  (- (* (/ *f0* (* *beta* *N* *fref*)) (+ 1 (* *alpha* *v0*))) (/ 1 *beta*)))
(defun gamma ()
  (/ (- 1 *Kt*) (* 2 31415926/10000000)))
(defun mu ()
  (/ *f0* (* *N* *fref*)))

; Define helper functions
(defun sign (x)
  (cond ((> x 0) 1)
        ((< x 0) -1)
        (t 0)))
(defun abslt (x)
  (cond ((>= x 0) x)
        (t (- 0 x))))

; The recurrence recDPLL-full(c,v,p) note: p for phase difference
(defun fdco (c v)
  (/ (+ 1 (* *alpha* v)) (+ 1 (* *beta* c))))
(defun recDPLL-full (c v p)
  (mv (+ c (* *g1* (sign p)))
      (+ v (* *g2* (- c *ccode*)))
      (+ (* (gamma) p) (- (* (mu) (fdco c v)) 1))))
; The recurrence recDPLL(c,p) only has the dynamics of c and p
(defun recDPLL (c p)
  (mv (+ c (* *g1* (sign p)))
      (+ (* (gamma) p) (- (* (mu) (fdco c *v0*)) 1))))
; The recurrence of c and p on the upper half of plane
(defun recDPLL-upper-C (c)
  (+ c *g1*))
(defun recDPLL-upper-P (c p)
  (+ (* (gamma) p) (- (* (mu) (fdco c *v0*)) 1)))
; The recurrence of c and p on the lower half of plane
(defun recDPLL-lower (c p)
  (mv (- c *g1*)
      (+ (* (gamma) p) (- (* (mu) (fdco c *v0*)) 1))))

; -------------------------------------------------------------------------
;; This part defines two ways of defining the sum to calculate p(j) and c(j)
;; when p > 0.
;; ------ Need a theorem to prove their equivalence.

; Using the summing formula
(defun c (m j)
  (* *g1* (+ m j)))
(defun state-j-sum-C (m j)
  (c m j))

; Represent a term of sum
(defun f-term (i args) (* (Expt (gamma) (- (nth 1 args) i)) ;; args - m, j 
                          (- (/ (* (mu) (+ 1 (* *alpha* *v0*)))
                                (+ 1 (* *beta* (c (nth 0 args) i)))) 1)))
; Represent sum
; Peel off first 2 terms, prove equivalence
(defun sum-p (jlo jhi args)
  (declare (xargs :measure (if (or (not (integerp jhi))
                                   (not (integerp jlo))
                                   (< jhi jlo))
                             0
                             (1+ (- jhi jlo)))))
  (if (or (not (integerp jhi)) (not (integerp jlo)) (< jhi jlo)) 0
    (+ (sum-p jlo (- jhi 1) args) (f-term jhi args))))

; Represent p
(defun state-j-sum-P (p0 m jhi)
  (if (zp jhi)
    p0
    (+ (* (Expt (gamma) jhi) p0) (sum-p 0 (- jhi 1) (list m (- jhi 1))))))

; Using the recurrence to calculate the sum
(defun state-j-rec-C (m j)
  (if (zp j)
    (* m *g1*)
    (recDPLL-upper-C (state-j-rec-C m (- j 1)))))
(defun state-j-rec-P (p0 m j)
  (if (zp j)
    p0
    (recDPLL-upper-P (state-j-rec-C m (- j 1)) (state-j-rec-P p0 m (- j 1)))))

;; ------ Need to prove p(2n-1) and when replacing i = h+n are the same
(defun n (m)
  (- (/ (equ-c) *g1*) m))

; Represent p(2n-1)
(defun p-2n-1 (p0 m)
  (state-j-sum-P p0 m (- (* 2 (n m)) 1)))

; Define a sum-p-1 corresponding to summation1
(defun sum-p-1 (jlo jhi k args)
  (declare (xargs :measure (if (or (not (integerp jhi))
                                   (not (integerp jlo))
                                   (< jhi jlo))
                             0
                             (1+ (- jhi jlo)))))
  (if (or (not (integerp jhi)) (not (integerp jlo)) (< jhi jlo)) 0
    (+ (f-term (+ jhi k) args) (sum-p-1 jlo (- jhi 1) k args))))

; Define a sum-p-2 corresponding to summation2
(defun sum-p-2 (jlo jhi args)
  (declare (xargs :measure (if (or (not (integerp jhi))
                                   (not (integerp jlo))
                                   (< jhi jlo))
                             0
                             (1+ (- jhi jlo)))))
  (if (or (not (integerp jlo)) (not (integerp jhi)) (< jhi jlo)) 0
    (+ (f-term jlo args) (sum-p-2 (+ jlo 1) jhi args))))

; Define a sum-p-3 corresponding to summation3
(defun sum-p-3 (jlo jhi k args)
  (declare (xargs :measure (if (or (not (integerp jhi))
                                   (not (integerp jlo))
                                   (< jhi jlo))
                             0
                             (1+ (- jhi jlo)))))
  (if (or (not (integerp jlo)) (not (integerp jhi)) (< jhi jlo)) 0
    (+ (f-term (+ jlo k) args) (sum-p-3 (+ jlo 1) jhi k args))))

; Define a sum-p-4 corresponding to summation4
(defun sum-p-4 (jlo jhi jlo-plus-jhi k args)
  (declare (xargs :measure (if (or (not (integerp jhi))
                                   (not (integerp jlo))
                                   (< jhi jlo))
                             0
                             (1+ (- jhi jlo)))))
  (if (or (not (integerp jlo)) (not (integerp jhi)) (< jhi jlo)) 0
    (+ (f-term (+ (- jlo-plus-jhi jhi) k) args) (sum-p-4 jlo (- jhi 1) jlo-plus-jhi k args))))

; Define a sum-p-full corresponding to summation1+summation2
(defun sum-p-full (jlo jhi jlo-plus-jhi k1 k2 args)
  (declare (xargs :measure (if (or (not (integerp jhi))
                                   (not (integerp jlo))
                                   (< jhi jlo))
                             0
                             (1+ (- jhi jlo)))))
  (if (or (not (integerp jlo)) (not (integerp jhi)) (< jhi jlo)) 0
    (+ (f-term (+ jhi k1) args)
       (f-term (+ (- jlo-plus-jhi jhi) k2) args)
       (sum-p-full jlo (- jhi 1) jlo-plus-jhi k1 k2 args))))



;; ---------------------------------------------------------------------- 
;; This part is the induction proof for the upper half space



;; ----------------------------------------------------------------------
;; This part defines two ways of defining the sum to calculate p(j) and c(j)
;; when p < 0.
;; ------ Need a theorem to prove their equivalence.
; 

;; ---------------------------------------------------------------------- 
;; This part is the induction proof for the lower half space

(in-package "ACL2")
(include-book "std/top" :dir :system)
(include-book "arithmetic/top-with-meta" :dir :system)

;; define the recurrence model
;; c-i+1 = min(max(c-i + g-c *sign(phi), c-min), c-max)
;; v-i+1 = min(max(v-i + g-v*(c-center - c) v-min), v-max)
;; phi-i+1 = wrap(phi-i + (f-dco(c-i, v-i) - f-ref) - g-phi * phi-i)
;; f-dco = (1+alpha*v-i)/(1+beta*c-i)*f-0
;; wrap(phi) = wrap(phi+1)  if phi <= -1
;;             phi          if -1<phi<1
;;             wrap(phi-1)  if phi >= 1

(defconst *g-c* 1/3200)
(defconst *g-v* (/ 1/3200 5))
(defconst *c-center* 1)
(defconst *g-phi* 4/5)
(defconst *N* 1)
(defconst *fref* 1)
(defconst *alpha* 1)
(defconst *beta* 1)
(defconst *f0* 1)

(defconst *c-min* 9/10)
(defconst *c-max* 11/10)
(defconst *v-min* 0)
(defconst *v-max* 2)

(defconst *c-equ* 1)
(defconst *v-equ* 1)
(defconst *phi-equ* 0)

(define c-i+1 (c-i phi-i)
  :guard (and (rationalp c-i) (rationalp phi-i))
  (min (max (+ c-i (* *g-c* (signum phi-i))) *c-min*) *c-max*))

(define v-i+1 (v-i c-i)
  :guard (and (rationalp c-i) (rationalp v-i))
  (min (max (+ v-i (* *g-v* (- *c-center* c-i))) *v-min*) *v-max*))

(defthm denominator-positive
  (>= (denominator i) 0))

()

;; -3.5 -> -2.5 -> 
(define wrap (phi)
  :guard (rationalp phi)
  :measure (cond ((>= phi 1) (nonnegative-integer-quotient (numerator (- phi 0)) (denominator (- phi 0))))
		 ((<= phi -1) (nonnegative-integer-quotient (- (numerator (- phi 0))) (denominator (- phi 0))))
		 (t 0))
  (cond ((<= phi -1) (wrap (+ phi 1)))
	((>= phi 1) (wrap (- phi 1)))
	(t phi)))

(define fdco (c v)
  :guard (and (raionalp c) (rationalp v))
  (/ (* *f0* (+ 1 (* *alpha* v))) (1+ (* *beta* c))))

(define phi-i+1 (c-i v-i phi-i)
  (wrap (+ phi-i
	   (- (fdco c-i v-i)
	      *fref*)
	   (- (* *g-phi* phi-i)))))

;; calculate the recurrence for n steps
(define DPLL-rec (c-i v-i phi-i n)
  (if (zp n)
      (mv c-i v-i phi-i)
      (DPLL-rec (c-i+1 c-i phi-i)
		(v-i+1 v-i c-i)
		(phi-i+1 c-i v-i phi-i)
		(1- n))))

(defun-sk DPLL-converge (c-i v-i phi-i)
  (exist n
	 (mv-let (c-res v-res phi-res)
		 (DPLL-rec c-i v-i phi-i n)
		 (and (< (abs (- c-res *c-equ*))
			 (abs (- c-i *c-equ*)))
		      (< (abs (- v-res *v-equ*))
			 (abs (- v-i *v-equ*)))
		      (< (abs (- phi-res *phi-equ*))
			 (abs (- phi-i *phi-equ*)))))))

(defthm DPLL-converge
  (implies (and (and (rationalp c-i)
		     (rationalp v-i)
		     (rationalp phi-i))
		(and (>= c-i *c-min*)
		     (<= c-i *c-max*)
		     (>= v-i *v-min*)
		     (<= v-i *v-max*)
		     (>= phi-i *phi-min*)
		     (<= phi-i *phi-max*)))
	   (DPLL-converge c-i v-i phi-i)))

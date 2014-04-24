;; test cases
:logic

;; test0
(defconst *a* 1)
(defun bar1 (x) (* 2 x))

;; a very simple theorem
(defthm test0
  (implies (and (and (rationalp x)) (and))
	   (equal (+ x x) (* *a* (bar1 x))))
  :hints
            (("Goal"
              :clause-processor
              (my-clause-processor clause '((bar1) 1 "test0")))))

;; test1
(defun foo1 (x y) (* x (+ 1 y)))

;; very first piece of test case
(thm (implies (and (and (rationalp x)
			(integerp y)
			(integerp z))
		   (and (not (<= x 0))
			(equal z (+ 3/2 4))
			(or (> x y) (> x (+ y 40/3)))))
	      (> (foo1 x (foo1 x z)) (foo1 x y)))
     :hints
            (("Goal"
              :clause-processor
              (my-clause-processor clause '((foo1) 2 "test1")))))

;; Test cases:
;; 1. Without constant definition and function definitions:
;;   a. all types
;;   b. all operators
;;   c. exceptional cases
;; 2. With constant definitions
;; 3. With function definitions

;; test2
;; We are assuming specific format for the declarations and conditions, use "and" in the connections:
;; implies ( - (and decl1 decl2 decl3 ...)
;;           \
;;             (and cond1 cond2 cond3 ...))
;;         (concl)

(defun foo (x) (+ x 3))
(defun bar (y) (* 2 (foo y)))

(defthm test2
  (implies (and (and (rationalp y))
		(and (> y 1)))
	   (> (bar (foo y)) 12))
  :hints
  (("Goal"
    :clause-processor
    (my-clause-processor clause '((foo bar) 5 "test2")))))

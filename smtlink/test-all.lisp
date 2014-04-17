;; test cases
:logic

;; test0
(defun bar (x) (* 2 x))

;; a very simple theorem
(defthm test0
  (implies (and (and (rationalp x)) (and))
	   (equal (+ x x) (bar x)))
  :hints
            (("Goal"
              :clause-processor
              (my-clause-processor clause '((bar) 1 "test0")))))

;; test1
(defun foo (x y) (* x y))

;; very first piece of test case
(thm (implies (and (and (rationalp x)
			(integerp y)
			(integerp z))
		   (and (not (<= x 0))
			(equal z (+ 2 4))
			(or (> x y) (> x (+ y 1)))))
	      (> (foo x (foo x z)) (foo x y)))
     :hints
            (("Goal"
              :clause-processor
              (my-clause-processor clause '((foo) 2 "test1")))))

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

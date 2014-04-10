;; test cases
:logic

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

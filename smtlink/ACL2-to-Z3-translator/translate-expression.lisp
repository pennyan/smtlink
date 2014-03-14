;; translate-expression contains functions for translating a SMT expression in ACL2 to Z3 expression
(in-package "ACL2")
(include-book "translate-number")
(include-book "translate-variable")
(include-book "translate-operator")
(include-book "../SMT-formula/checker/is-SMT-number")
(include-book "../SMT-formula/checker/is-SMT-variable")
(include-book "../SMT-formula/checker/is-SMT-operator")

;; This is the version that I don't care about whether that's a function body expression, or hypothesis and conclusion expression, or function call expression. I find if I want to integrate the concept of a function, I can't mpossibly distinguish between these concepts.


;;SMT-variable

(mutual-recursion
;; translate-expression-long
(defun translate-expression-long (expression)
  "translate-expression-long: translate a SMT expression's parameters in ACL2 into Z3 expression"
  (if (consp (cdr expression))
      (cons (translate-expression (car expression))
	    (cons '\, (translate-expression-long (cdr expression))))
    (translate-expression (car expression))))

;; translate-expression
(defun translate-expression (expression)
  "translate-expression: translate a SMT expression in ACL2 to Z3 expression"
  (if (consp expression)
      (cond ((is-SMT-operator (car expression)) 
	     (list (translate-operator (car expression))
		   '\(
		   (translate-expression-long (cdr expression))
		   '\)))
	    (t (cw "Error: This is not a valid function: ~q0" (car expression))))
    (cond ((is-SMT-number expression) (translate-number expression))
	  ((is-SMT-variable expression) (translate-variable expression))
	  (t (cw "Error: Invalid number or variable: ~q0" expression)))))
)



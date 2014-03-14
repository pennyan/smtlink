;; SMT-expression contains function defining an SMT 
;; expression that is build upon
;; arithmetic, comparison and logic operators. 
(in-package "ACL2")
(include-book "../checker/is-SMT-logic")
(include-book "SMT-logic")
(include-book "../checker/is-SMT-comparison")
(include-book "SMT-comparison")
(include-book "../checker/is-SMT-number")
(include-book "SMT-number")
(include-book "../checker/is-SMT-variable")
(include-book "SMT-variable")
(include-book "../checker/is-SMT-arithmetic")
(include-book "SMT-arithmetic")
(include-book "../checker/is-SMT-comparison")
(include-book "SMT-comparison")
(include-book "../checker/is-SMT-function-existing")
(include-book "SMT-function-exist")

;; function <- expression | arithmetic
;; expression <- logic
;; logic <- logic | comparison
;; comparison <- arithmetic
;; Q: Should it be my job or the user's job to make sure that there's no mix of different type of functions?
;;    I'm asumming the type of function matches the place it is inserted by the user.

(mutual-recursion
;; SMT-arithmetic-expression-long
(defun SMT-arithmetic-expression-long (expression)
  "SMT-arithmetic-expression-long: the multiple operands of an + or * expression"
  (if (consp expression)
      (cons (SMT-arithmetic-expression (car expression)) 
	    (SMT-arithmetic-expression-long (cdr expression)))
    nil))

;; SMT-arithmetic-expression
(defun SMT-arithmetic-expression (expression)
  "SMT-arithmetic-expression: a SMT arithmetic expression"
  (if (consp expression)
      (cond ((is-SMT-arithmetic (car expression)) 
	     (cond ((or (is-SMT-plus (car expression)) (is-SMT-multiply (car expression))) 
		    (cons (SMT-arithmetic (car expression))
			  (SMT-arithmetic-expression-long (cdr expression))))
		   (t 
		    (if (equal (len (cdr expression)) 2)
			(list (SMT-arithmetic (car expression)) 
			      (SMT-arithmetic-expression (cadr expression)) 
			      (SMT-arithmetic-expression (caddr expression)))
		      (cw "Error: Wrong number of operands: ~q0" expression)))))
	    ((is-SMT-function-existing (car expression))
	     (cons (SMT-function-exist (car expression))
		   (SMT-arithmetic-expression-long (cdr expression))))
	    (t (cw "Error: Invalid arithmetic operator: ~q0" (car expression))))
    (cond ((is-SMT-number expression) (SMT-number expression))
	  ((is-SMT-variable expression) (SMT-variable expression))
	  (t (cw "Error: Invalid number or variable: ~q0" expression)))))
)

;; SMT-comparison-expression
(defun SMT-comparison-expression (expression)
  "SMT-comparison-expression: a SMT comparison expression"
  (if (not (equal (len expression) 3))
      (cw "Error: Wrong number of operands in a SMT comparison expression: ~q0" expression)
    (let ((oprt (car expression))
	  (exp1 (cadr expression))
	  (exp2 (caddr expression)))
      (list (SMT-comparison oprt)
	    (SMT-arithmetic-expression exp1)
	    (SMT-arithmetic-expression exp2)))))

(mutual-recursion
 ;; SMT-logic-expression-long
 (defun SMT-logic-expression-long (expression)
   "SMT-logic-expression-long: the multiple operands of an and or or expression"
   (if (consp expression)
       (cons (SMT-logic-expression (car expression)) 
	     (SMT-logic-expression-long (cdr expression)))
     nil))

 ;; SMT-logic-expression
 (defun SMT-logic-expression (expression)
   "SMT-logic-expression: a SMT expression made of logic expressions, or comparisons"
   (if (consp expression)
       (cond ((is-SMT-comparison (car expression)) 
	      (SMT-comparison-expression expression))
	     ((is-SMT-logic (car expression)) 
	      (cond ((or (is-SMT-and (car expression)) 
			 (is-SMT-or (car expression)))
		     (cons (SMT-logic (car expression))
			   (SMT-logic-expression-long (cdr expression))))
		    ((is-SMT-not (car expression))
		     (if (equal (len (cdr expression)) 1)
			 (list (SMT-not (car expression))
			       (SMT-logic-expression (cadr expression)))
		       (cw "Error: Wrong number of operands in a not expression: ~q0" expression)))))
	     ((is-SMT-function-existing (car expression))
	       (cons (SMT-function-exist (car expression))
		     (SMT-logic-expression-long (cdr expression))))
	      (t (cw "Error: Invalid SMT logic expression: ~q0" expression)))
     (cond ((is-SMT-number expression) (SMT-number expression))
	   ((is-SMT-variable expression) (SMT-variable expression))
	   (t (cw "Error: Invalid variable: ~q0" expression)))))
 )


(mutual-recursion
;; SMT-fun-input-expression-long
(defun SMT-fun-input-expression-long (expression)
  "SMT-fun-input-expression-long: inputs of a SMT function expression"
  (if (consp expression)
      (cons (SMT-fun-expression (car expression)) 
	    (SMT-fun-input-expression-long (cdr expression)))
    nil))

;; SMT-fun-expression
(defun SMT-fun-expression (expression)
  "SMT-fun-expression: a SMT expression for function body"
  (if (consp expression)
      (cond ((is-SMT-arithmetic (car expression)) 
	     (SMT-arithmetic-expression expression))
	    ((or (is-SMT-logic (car expression))
		 (is-SMT-comparison (car expression)))
	     (SMT-logic-expression expression))
	    ((is-SMT-function-existing (car expression))
	     (cons (SMT-function-exist (car expression))
		   (SMT-fun-input-expression-long (cdr expression))))
	    (t
	     (cw "Error: This is not a valid SMT function: ~q0" (car expression))))
    (cond ((is-SMT-number expression) (SMT-number expression))
	  ((is-SMT-variable expression) (SMT-variable expression))
	  (t (cw "Error: Invalid number or variable: ~q0" expression)))))
)

;; SMT-expression
(defun SMT-expression (expression)
  "SMT-expression: a SMT expression made of arithmetic, comparison and logic formulas"
  (if (not (listp expression))
      (cw "Error: The SMT expression is not a list: ~q0" expression)
    (SMT-logic-expression expression)))


;; SMT-expression contains function defining an SMT 
;; expression that is build upon
;; arithmetic, comparison and logic operators. 
(in-package "ACL2")

;; note: expressions are logic expressions
;; expression <- logic
;; logic <- logic | comparison
;; comparison <- arithmetic

;; SMT-arithmetic-expression


;; SMT-comparison-expression


;; SMT-logic-expression
(defun SMT-logic-expression (expression)
  "SMT-logic-expression: a SMT expression made of logic expressions, or comparisons"
  (if ))

;; SMT-expression
(defun SMT-expression (expression)
  "SMT-expression: a SMT expression made of arithmetic, comparison and logic formulas"
  (if (not (listp expression))
      (cw "Error: The SMT expression is not a list: ~q0" expression)
    (SMT-logic-expression expression)))

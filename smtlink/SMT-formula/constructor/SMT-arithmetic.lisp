;; SMT-arithmetic contains functions for defining symbols for arithmetic operations
(in-package "ACL2")

;; SMT-plus
(defun SMT-plus (operator)
  "SMT-plus: the symbol for arithmetic plus"
  (if (equal operator '+)
      operator
    (cw "Error: This is not a valid plus operator: ~q0" operator)))

;; SMT-minus
(defun SMT-minus (operator)
  "SMT-minus: the symbol for arithmetic minus"
  (if (equal operator '-)
      operator
    (cw "Error: This is not a valid minus operator: ~q0" operator)))

;; SMT-multiply
(defun SMT-multiply (operator)
  "SMT-multiply: the symbol for arithmetic multiply"
  (if (equal operator '*)
      operator
    (cw "Error: This is not a valid multiply operator: ~q0" operator)))

;; SMT-divide
(defun SMT-divide (operator)
  "SMT-divide: the symbol for arithmetic divide"
  (if (equal operator '/)
      operator
    (cw "Error: This is not a valid divide operator: ~q0" operator)))

;; SMT-arithmetic
(defun SMT-arithmetic (operator)
  "SMT-arithmetic: the symbols for arithmetic operators"
  (cond ((equal operator '+) (SMT-plus operator))
	((equal operator '-) (SMT-minus operator))
	((equal operator '*) (SMT-multiply operator))
	((equal operator '/) (SMT-divide operator))
	(t (cw "Error: There exists no such arithmetic operator in SMT-formula: ~q0" operator))))

;; is-SMT-arithmetic contains functions for checking if it is a symbol for arithmetic operations
(in-package "ACL2")

;; is-SMT-plus
(defun is-SMT-plus (operator)
  "is-SMT-plus: Check if it is a symbol for arithmetic plus"
  (if (equal operator '+) t nil))

;; is-SMT-minus
(defun is-SMT-minus (operator)
  "is-SMT-minus: Check if it is a symbol for arithmetic minus"
  (if (equal operator '-) t nil))

;; is-SMT-multiply
(defun is-SMT-multiply (operator)
  "is-SMT-multiply: Check if it is a symbol for arithmetic multiply"
  (if (equal operator '*) t nil))

;; is-SMT-divide
(defun is-SMT-divide (operator)
  "is-SMT-divide: Check if it is a symbol for arithmetic divide"
  (if (equal operator '/) t nil))

;; is-SMT-arithmetic
(defun is-SMT-arithmetic (operator)
  "is-SMT-arithmetic: Check if it is a symbols for arithmetic operators"
  (cond ((is-SMT-plus operator) t)
	((is-SMT-minus operator) t)
	((is-SMT-multiply operator) t)
	((is-SMT-divide operator) t)
	(t nil)))

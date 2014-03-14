;; SMT-logic contains functions for boolean logic operator symbols
(in-package "ACL2")

;; SMT-and
(defun SMT-and (operator)
  "SMT-and: This is the logic symbol for and"
  (if (equal operator 'and)
      operator
    (cw "Error: This is not a valid and operator: ~q0" operator)))

;; SMT-or
(defun SMT-or (operator)
  "SMT-or: This is the logic symbol for or"
  (if (equal operator 'or)
      operator
    (cw "Error: This is not a valid or operator: ~q0" operator)))

;; SMT-not
(defun SMT-not (operator)
  "SMT-not: This is the logic symbol for not"
  (if (equal operator 'not)
      operator
    (cw "Error: This is not a valid not operator: ~q0" operator)))

;; SMT-logic
(defun SMT-logic (operator)
  "SMT-logic: defines SMT boolean logic operator symbols"
  (cond ((equal operator 'and) (SMT-and operator))
	((equal operator 'or) (SMT-or operator))
	((equal operator 'not) (SMT-not operator))
	(t (cw "Error: There exists no such boolean logic operator in SMT-formula: ~q0" operator))))

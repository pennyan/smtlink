;; SMT-comparison contains functions for SMT comparison operators
(in-package "ACL2")

;; SMT-equal
(defun SMT-equal (operator)
  "SMT-equal: This is the comparison symbol for equal"
  (if (equal operator 'equal)
      operator
    (cw "Error: This is not a valid equal-to operator: ~q0" operator)))

;; SMT-greater-than
(defun SMT-greater-than (operator)
  "SMT-greater-than: This is the comparison symbol for >"
  (if (equal operator '>)
      operator
    (cw "Error: This is not a valid greater-than operator: ~q0" operator)))

;; SMT-greater-equal
(defun SMT-greater-equal (operator)
  "SMT-greatere-equal: This is the comparison symbol for >="
  (if (equal operator '>=)
      operator
    (cw "Error: This is not a valid greater-or-equal-to operator: ~q0" operator)))

;; SMT-smaller-than
(defun SMT-smaller-than (operator)
  "SMT-smaller-than: This is the comparison symbol for <"
  (if (equal operator '<)
      operator
    (cw "Error: This is not a valid smaller-than operator: ~q0" operator)))
;; SMT-smaller-equal
(defun SMT-smaller-equal (operator)
  "SMT-smaller-equal: This is the comparison symbol for <="
  (if (equal operator '<=)
      operator
    (cw "Error: This is not a valid smaller-or-equal-to operator: ~q0" operator)))

;; SMT-comparison
(defun SMT-comparison (operator)
  "SMT-comparison: defines SMT comparison operator symbols"
  (cond ((equal operator 'equal) (SMT-equal operator)) 
	((equal operator '>) (SMT-greater-than operator))
	((equal operator '>=) (SMT-greater-equal operator))
	((equal operator '<) (SMT-smaller-than operator))
	((equal operator '<=) (SMT-smaller-equal operator))
	(t (cw "Error: There exists no such comparison operator in SMT-formula: ~q0" operator))))

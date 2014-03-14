;; is-SMT-comparison contains functions for SMT comparison operators
(in-package "ACL2")

;; is-SMT-equal
(defun is-SMT-equal (operator)
  "is-SMT-equal: Check if this is the comparison symbol for equal"
  (if (equal operator 'equal) t nil))

;; is-SMT-greater-than
(defun is-SMT-greater-than (operator)
  "is-SMT-greater-than: Check if this is the comparison symbol for >"
  (if (equal operator '>) t nil))

;; is-SMT-greater-equal
(defun is-SMT-greater-equal (operator)
  "is-SMT-greater-equal: Check if this is the comparison symbol for >="
  (if (equal operator '>=) t nil))

;; is-SMT-smaller-than
(defun is-SMT-smaller-than (operator)
  "is-SMT-smaller-than: Check if this is the comparison symbol for <"
  (if (equal operator '<) t nil))

;; is-SMT-smaller-equal
(defun is-SMT-smaller-equal (operator)
  "is-SMT-smaller-equal: Check if this is the comparison symbol for <="
  (if (equal operator '<=) t nil))

;; is-SMT-comparison
(defun is-SMT-comparison (operator)
  "is-SMT-comparison: Check if this is a SMT comparison operator symbol"
  (cond ((is-SMT-equal operator) t) 
	((is-SMT-greater-than operator) t)
	((is-SMT-greater-equal operator) t)
	((is-SMT-smaller-than operator) t)
	((is-SMT-smaller-equal operator) t)
	(t nil)))

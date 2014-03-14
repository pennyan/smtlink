;; is-SMT-logic contains functions for boolean logic operator symbols
(in-package "ACL2")

;; is-SMT-and
(defun is-SMT-and (operator)
  "is-SMT-and: Check if this is the logic symbol for and"
  (if (equal operator 'and) t nil))

;; is-SMT-or
(defun is-SMT-or (operator)
  "is-SMT-or: Check if this is the logic symbol for or"
  (if (equal operator 'or) t nil))

;; is-SMT-not
(defun is-SMT-not (operator)
  "is-SMT-not: Check if this is the logic symbol for not"
  (if (equal operator 'not) t nil))

;; is-SMT-logic
(defun is-SMT-logic (operator)
  "is-SMT-logic: check if this is a SMT boolean logic operator symbol"
  (cond ((is-SMT-and operator) t)
	((is-SMT-or operator) t)
	((is-SMT-not operator) t)
	(t nil)))

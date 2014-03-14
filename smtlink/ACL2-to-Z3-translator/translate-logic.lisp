;; translate-logic contains functions for translating logic operators in SMT-formula of ACL2 into Z3
(in-package "ACL2")

;; translate-and
(defun translate-and (operator)
  "translate-and: translate an and operator in SMT-formula into Z3"
  "acl2_and")

;; translate-or
(defun translate-or (operator)
  "translate-or: translate an or operator in SMT-formula into Z3"
  "acl2_or")

;; translate-not
(defun translate-not (operator)
  "translate-not: translate a not operator in SMT-formula into Z3"
  "acl2_not")

;; translate-logic
(defun translate-logic (operator)
  "translate-logic: translate a logic operator in SMT-formula into Z3"
  (cond ((equal operator 'and) (translate-and operator))
	((equal operator 'or) (translate-or operator))
	(t (translate-not operator))))

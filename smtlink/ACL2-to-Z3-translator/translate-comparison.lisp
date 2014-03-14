;; translate-comparison contains functions for translating comparison operators in SMT-formula of ACL2 into Z3 
(in-package "ACL2")

;; translate-equal 
(defun translate-equal (operator)
  "translate-equal: translate equal operator in SMT-formula into Z3"
  "acl2_equal")

;; translate-greater-than
(defun translate-greater-than (operator)
  "translate-greater-than: translate greater than operator in SMT-formula into Z3"
  "acl2_gt")

;; translate-greater-equal 
(defun translate-greater-equal (operator)
  "translate-greater-equal: translate greater-or-equal-to operator in SMT-formula into Z3"
  "acl2_get")

;; translate-smaller-than
(defun translate-smaller-than (operator)
  "translate-smaller-than: translate smaller-than operator in SMT-formula into Z3"
  "acl2_st")

;; translate-smaller-equal
(defun translate-smaller-equal (operator)
  "translate-smaller-equal: translate smaller-or-equal-to operator in SMT-formula into Z3"
  "acl2_set")

;; transalate-comparison
(defun translate-comparison (operator)
  "translate-comparison: translate comparison operators in SMT-formula into Z3"
  (cond ((equal operator 'equal) (translate-equal operator))
	((equal operator '>) (translate-greater-than operator))
	((equal operator '>=) (translate-greater-equal operator))
	((equal operator '<) (translate-smaller-than operator))
	((equal operator '<=) (translate-smaller-equal operator))))

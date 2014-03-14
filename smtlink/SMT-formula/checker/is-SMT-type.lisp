;; is-SMT-type contains functions for checking if a symbol is a SMT-type
;; See the documentation for more information
(in-package "ACL2")

;; is-SMT-real
(defun is-SMT-real (type)
  "is-SMT-real: Check if this is a real declaration symbol"
  (cond ((equal type 'RATIONALP) t) 
	((equal type 'ACL2-NUMBERP) t)
	((equal  type 'COMPLEX-RATIONALP) t)
	(t nil)))

;; is-SMT-integer
(defun is-SMT-integer (type)
  "is-SMT-integer: Check if this is an integer declaration symbol"
  (if (equal type 'INTEGERP) t nil))

;; is-SMT-type: type declaration symbols
(defun is-SMT-type (type)
  "is-SMT-type: Check if this is a type declaration symbol"
  (cond ((is-SMT-real type) t)
	((is-SMT-integer type) t)
	(t nil)))

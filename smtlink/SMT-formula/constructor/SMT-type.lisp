;; SMT-type contains functions for constructing a SMT-type
;; See the documentation for more information
(in-package "ACL2")

;; SMT-real
(defun SMT-real (type)
  "SMT-real: real declaration symbols"
  (cond ((equal type 'RATIONALP) 'RATIONALP) 
	((equal type 'ACL2-NUMBERP) 'ACL2-NUMBERP)
	((equal type 'COMPLEX-RATIONALP) 'COMPLEX-RATIONALP)
	(t (cw "Error: Input is not a valid real symbol: ~q0" type))))

;; SMT-integer
(defun SMT-integer (type)
  "SMT-integer: integer declaration symbols"
  (if (equal type 'INTEGERP)
      type
    (cw "Error: Input is not a valid integer symbol: ~q0" type)))

;; SMT-type: type declaration symbols
(defun SMT-type (type)
  "SMT-type: type declaration symbols"
  (cond ((or (equal type 'RATIONALP)
	     (equal type 'ACL2-NUMBERP)
	     (equal type 'COMPLEX-RATIONALP))
	 (SMT-real type))
	((equal type 'INTEGERP) (SMT-integer type))
	(t (cw "Error: There exist no such type in ACL2: ~q0" type))))

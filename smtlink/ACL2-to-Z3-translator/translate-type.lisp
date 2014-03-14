;; translate-type contains functions for translating a type in ACL2 SMT-formula into Z3 type
(in-package "ACL2")

;; translate-real
(defun translate-real (type)
  "translate-real: translate into real type in Z3"
  "Real")

;; translate-integer
(defun translate-integer (type)
  "translate-integer: translate into integer type in Z3"
  "Int")

;; translate-type
(defun translate-type (type)
  "translate-type: translates a type in ACL2 SMT-formula into Z3 type"     ;; all using reals because Z3 is not very good at mixed types
  (cond ((or (equal type 'RATIONALP)
	     (equal type 'ACL2-NUMBERP)
	     (equal type 'COMPLEX-RATIONALP))
	 (translate-real type))
	(t (translate-real type))))
     ;; integer case
     ;; (t (translate-integer type))

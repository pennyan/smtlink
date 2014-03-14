;; translator-arithmetic contains functions for translating an arithmetic operator in SMT-formula of ACL2 into Z3
(in-package "ACL2")

;; translate-plus 
(defun translate-plus (operator)
  "translate-plus: translate a plus operator into Z3 function"
  "acl2_plus")

;; translate-minus 
(defun translate-minus (operator)
  "translate-minus: translate a minus operator into Z3 function"
  "acl2_minus")

;; translate-multiply
(defun translate-multiply (operator)
  "translate-multiply: translate a multiply operator into Z3 function"
  "acl2_multiply")

;; translate-divide
(defun translate-divide (operator)
  "translate-divide: translate a divide operator into Z3 function"
  "acl2_divide")

;; translate-arithmetic
(defun translate-arithmetic (operator)
  "translate-arithmetic: translates an arithmetic operator in a SMT-formula of ACL2 into Z3"
  (cond ((equal operator '+) (translate-plus operator))
	((equal operator '-) (translate-minus operator))
	((equal operator '*) (translate-multiply operator))
	(t (translate-divide operator))))

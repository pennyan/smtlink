;; translate-conclusion contains functions for translating a SMT-formula conclusion statement into Z3
(in-package "ACL2")
(include-book "translate-expression")

;; translate-conclusion-list
(defun translate-conclusion-list (concl-list)
  "translate-conclusion-list: translate a SMT-formula conclusion statement into Z3"
  (list (cons "conclusion" 
	      (cons '= (translate-expression concl-list))) #\Newline))

;; translate-hypothesis contains functions for translating a SMT-formula hypothesis statement into Z3
(in-package "ACL2")
(include-book "translate-expression")

;; translate-hypothesis-list
(defun translate-hypothesis-list (hyp-list)
  "translate-hypothesis-list: translate a SMT-formula hypothesis statement into Z3"
  (list (cons "hypothesis" 
	      (cons '= (translate-expression hyp-list))) #\Newline))

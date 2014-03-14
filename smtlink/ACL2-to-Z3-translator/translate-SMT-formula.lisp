;; translate-SMT-formula contains functions for translating the whole SMT-formula into Z3
(in-package "ACL2")
(include-book "translate-constant")
(include-book "translate-function")
(include-book "translate-declaration")
(include-book "translate-hypothesis")
(include-book "translate-conclusion")
(include-book "translate-theorem")

;; translate-SMT-formula
(defun translate-SMT-formula (formula)
  "translate-SMT-formula: translate the whole SMT-formula into Z3"
  (let ((const-list (car formula))
	(func-list (cadr formula))
	(decl-list (caddr formula))
	(hyp-list (cadddr formula))
	(concl-list (car (cddddr formula))))
    (list (translate-constant-list const-list)
	  (translate-function-list func-list)
	  (translate-declaration-list decl-list)
	  (translate-hypothesis-list hyp-list)
	  (translate-conclusion-list concl-list)
	  (translate-theorem ))))

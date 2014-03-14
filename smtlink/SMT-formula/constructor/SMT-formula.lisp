;; SMT-formula contains functions for building a SMT formula
;; A SMT-formula is consisted of below parts:
;; ( SMT-constant-list
;;   SMT-function-list
;;   SMT-declaration-list
;;   SMT-hypothesis-list
;;   SMT-conclusion-list )
(in-package "ACL2")
(include-book "SMT-constant")
(include-book "SMT-function")
(include-book "SMT-declaration")
(include-book "SMT-hypothesis")
(include-book "SMT-conclusion")

;; SMT-formula
(defun SMT-formula (const-list
		    func-list
		    decl-list
		    hyp-list
		    concl-list)
  "SMT-formula: This is a SMT formula"
  (list (SMT-constant-list const-list)
	(SMT-function-list func-list)
	(SMT-declaration-list decl-list)
	(SMT-hypothesis-list hyp-list)
	(SMT-conclusion-list concl-list))
  )

;; SMT-formula-top
(defmacro SMT-formula-top (&key const-list
				func-list
				decl-list
				hyp-list
				concl-list)
  "SMT-formula-top: This is a macro for fetching parameters of a SMT formula"
  (list 'quote (SMT-formula const-list 
			   func-list 
			   decl-list 
			   hyp-list 
			   concl-list))
  )

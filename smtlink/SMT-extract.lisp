;; SMT-extract extracts the declarations, hypotheses and conclusion from a SMT formula in ACL2.
;; A typical SMT formula is in below format:
;; (implies (and <decl-list>
;;               <hypo-list>)
;;          <concl-list>)

(in-package "ACL2")
(include-book "./helper")

;; get-orig-param
(defun get-orig-param (decl-list)
  "get-orig-param: given a declaration list of a SMT formula, return a list of variables appearing in the declaration list"
  (if (atom decl-list)
      (cond ((or (equal decl-list 'if)
		 (equal decl-list 'nil)
		 (equal decl-list 'rationalp)
		 (equal decl-list 'integerp)
		 (equal decl-list 'quote))
	     nil)
	    (t decl-list))
      (combine (get-orig-param (car decl-list))
	       (get-orig-param (cdr decl-list)))))

;; SMT-extract
(defun SMT-extract (term)
  "extract decl-list, hypo-list and concl from a ACL2 term"
  (let ((decl-list (cadr (cadr term)))
	(hypo-list (caddr (cadr term)))
	(concl-list (caddr term)))
    (mv decl-list hypo-list concl-list)))

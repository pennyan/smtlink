;; SMT-extract extracts the declarations, hypotheses and conclusion from a SMT formula in ACL2.
;; A typical SMT formula is in below format:
;; (implies (and <decl-list>
;;               <hypo-list>)
;;          <concl-list>)

;; SMT-extract
(defun SMT-extract (term)
  "extract decl-list, hypo-list and concl from a ACL2 term"
  (let ((decl-list (cadr (cadr term)))
	(hypo-list (caddr (cadr term)))
	(concl-list (caddr term)))
    (prog2$ (cw "extract: ~q0 ~q1 ~q2" decl-list hypo-list concl-list)
	    (mv decl-list hypo-list concl-list))))

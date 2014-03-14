;; translate-declaration contains functions for translating a declaration list in a SMT formula into a list of Z3 declaration code.
(in-package "ACL2")
(include-book "translate-type")
(include-book "translate-variable")

;; translate-declaration
(defun translate-declaration (decl)
  "translate-declaration: translate a declaration in ACL2 SMT formula into Z3 declaration"
  (let ((type (car decl))
	(name (cadr decl)))
    (list (translate-variable name) '= (translate-type type) '\(  '\" (translate-variable name) '\" '\))))

;; translate-declaration-list
(defun translate-declaration-list (decl-list)
  "translate-declaration-list: translate a list of SMT-formula declarations into Z3 code"
  (if (consp decl-list)
      (cons (translate-declaration (car decl-list))
	    (cons #\Newline (translate-declaration-list (cdr decl-list))))
    nil))

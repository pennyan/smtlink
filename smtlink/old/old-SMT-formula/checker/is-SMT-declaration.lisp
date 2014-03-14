;; is-SMT-declaration contains functions for SMT variable declarations
(in-package "ACL2")
(include-book "is-SMT-type")
(include-book "is-SMT-variable")

;; is-SMT-declaration 
(defun is-SMT-declaration (decl)
  "is-SMT-declaration: Check if this is a SMT variable declaration"
  (if (not (equal (len decl) 2)) nil
    (let ((type (car decl))
	  (name (cadr decl)))
      (if (and (is-SMT-type type)
	       (is-SMT-variable name)) t nil))))

;; is-SMT-declaration-list-help
(defun is-SMT-declaration-list-help (decl-list)
  "is-SMT-declaration-list-help: Check if this is a list of SMT variable declarations, the helper function"
  (if (consp decl-list)
      (if (is-SMT-declaration (car decl-list)) 
	  (is-SMT-declaration-list-help (cdr decl-list))
	nil)
    t))

;; is-SMT-declaration-list
(defun is-SMT-declaration-list (decl-list)
  "is-SMT-declaration-list: Check if this is a list of SMT variable declarations"
  (if (not (listp decl-list)) nil
    (is-SMT-declaration-list-help decl-list)))

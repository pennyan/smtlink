;; SMT-declaration contains functions for SMT variable declarations
(in-package "ACL2")
(include-book "SMT-type")
(include-book "SMT-variable")

;; SMT-declaration 
(defun SMT-declaration (decl)
  "SMT-declaration: This is a SMT variable declaration"
  (if (not (equal (len decl) 2))
      (cw "Error: Wrong number of elements in a variable declaration list: ~q0" decl)
    (let ((type (car decl))
	  (name (cadr decl)))
      (list (SMT-type type) (SMT-variable name)))))

;; SMT-declaration-list-help
(defun SMT-declaration-list-help (decl-list)
  "SMT-declaration-list-help: This is a list of SMT variable declarations, the helper function"
  (if (consp decl-list)
      (cons (SMT-declaration (car decl-list)) (SMT-declaration-list-help (cdr decl-list)))
    nil))

;; SMT-declaration-list
(defun SMT-declaration-list (decl-list)
  "SMT-decl-list: This is a list of SMT variable declarations"
  (if (not (listp decl-list))
      (cw "Error: The SMT declaration list is not in the right form: ~q0" decl-list)
    (SMT-declaration-list-help decl-list)))

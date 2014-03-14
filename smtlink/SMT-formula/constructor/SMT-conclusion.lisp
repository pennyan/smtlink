;; SMT-conclusion.lisp contains functions for building conclusions of a SMT formula
(in-package "ACL2")
(include-book "SMT-expression")

;; SMT-conclusion-list
(defun SMT-conclusion-list (concl-list)
  "SMT-conclusion-list: This is a SMT conclusion list"
  (if (not (listp concl-list))
      (cw "Error: The SMT conclusion list is not in the right form: ~q0" concl-list)
    (SMT-expression concl-list)))


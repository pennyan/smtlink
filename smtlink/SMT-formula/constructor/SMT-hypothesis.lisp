;; SMT-hypothesis contains functions for building hypothesis of a SMT formula
(in-package "ACL2")
(include-book "SMT-expression")

;; SMT-hypothesis-list
(defun SMT-hypothesis-list (hyp-list)
  "SMT-hypothesis-list: This is a SMT hypothesis list"
  (if (not (listp hyp-list))
      (cw "Error: The SMT hypothesis list is not in the right form: ~q0" hyp-list)
    (SMT-expression hyp-list)))

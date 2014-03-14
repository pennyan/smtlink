;; SMT-variable contain function for constructing a SMT variable
(in-package "ACL2")

;; SMT-variable
(defun SMT-variable (name)
  "SMT-variable: This is a SMT variable name"
  (if (symbolp name)
      name
    (cw "Error: This is not a valid SMT variable name: ~q0" name)))

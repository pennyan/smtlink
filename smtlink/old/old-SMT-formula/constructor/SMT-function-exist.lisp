;; SMT-function-exist contains function for checking if a SMT function exist in the function list. 
;; Not implemented for now.
(in-package "ACL2")

;; SMT-function-exist
(defun SMT-function-exist (name)
  "SMT-function-exist: construct a function symbol that exist in function list"
  (if (symbolp name)
      name
    (cw "Error: This function does not exist: ~q0" name)))

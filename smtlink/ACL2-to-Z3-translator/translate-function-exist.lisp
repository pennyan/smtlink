;; translate-function-exist translate a function after checking if a SMT function exist in the function list. 
;; Not implemented for now.
(in-package "ACL2")

;; translate-function-exist
(defun translate-function-exist (name)
  "translate-function-exist: translate a function symbol that exist in function list"
  (if (symbolp name)
      name
    (cw "Error: This function does not exist: ~q0" name)))

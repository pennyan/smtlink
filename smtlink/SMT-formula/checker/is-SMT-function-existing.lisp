;; is-SMT-function-existing contains function for checking if a SMT function symbol is in the function list. 
;; Not implemented for now.
(in-package "ACL2")

;; is-SMT-function-existing
(defun is-SMT-function-existing (name)
  "is-SMT-function-existing: Check if the use of a function exists in the function list"
  (if (symbolp name) t nil))

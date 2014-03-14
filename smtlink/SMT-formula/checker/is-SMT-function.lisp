;; is-SMT-function contains functions for checking if a list is a SMT-function
(in-package "ACL2")

;; is-SMT-fun-name
;; I want this to be able to figure out if that's a name mentioned in the function list in the future
(defun is-SMT-fun-name (name)
  "is-SMT-fun-name: Check if this is a SMT function name symbol"
  (if (symbolp name) t nil))

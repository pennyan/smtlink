;; is-SMT-variable contains function for checking if a variable is a SMT variable
(in-package "ACL2")

;; is-SMT-variable
(defun is-SMT-variable (var)
  "is-SMT-variable: check if a variable is a SMT var"
  (if (symbolp var) t nil))

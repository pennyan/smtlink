;; SMT-constant contains functions for constructing and identifying SMT constant declarations
(in-package "ACL2")
(include-book "SMT-number")

;; SMT-constant-name
(defun SMT-constant-name (name)
  "SMT-constant-name: This is a SMT constant name"
  (if (symbolp name)
      name
    (cw "Error: This is not a valid SMT constant name: ~q0" name)))

;; SMT-constant
(defun SMT-constant (constant)
  "SMT-constant: This is a SMT constant declaration"
  (if (not (equal (len constant) 2))
      (cw "Error: Wrong number of elements in a constant declaration list: ~q0" constant)
    (let ((name (car constant)) 
	  (value (cadr constant)))
      (list (SMT-constant-name name) (SMT-number value)))))


;; SMT-constant-list-help
(defun SMT-constant-list-help (constant-list)
  "SMT-constant-list: This is a list of SMT constant declarations, the helper function"
  (if (consp constant-list)
      (cons (SMT-constant (car constant-list)) (SMT-constant-list-help (cdr constant-list)))
    nil))

;; SMT-constant-list
(defun SMT-constant-list (constant-list)
  "SMT-constant-list: This is a list of SMT constant declarations"
  (if (not (listp constant-list))
      (cw "Error: The SMT constant list is not in the right form: ~q0" constant-list)
    (SMT-constant-list-help constant-list)))

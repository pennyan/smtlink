;; is-SMT-constant contains functions for checking if the input are SMT constant declarations
(in-package "ACL2")
(include-book "is-SMT-number")

;; is-SMT-constant-name
(defun is-SMT-constant-name (name)
  "is-SMT-constant-name: Check if this is a SMT constant name"
  (if (symbolp name) t nil))

;; is-SMT-constant
(defun is-SMT-constant (constant)
  "is-SMT-constant: Check if this is a SMT constant declaration"
  (if (not (equal (len constant) 3)) nil
    (let ((name (car constant)) 
	  (sign (cadr constant)) 
	  (value (caddr constant)))
      (cond ((and (not (equal sign '=))
		  (not (is-SMT-constant-name name))
		  (not (is-SMT-number value))) 
	     nil)
	    (t t)))))


;; is-SMT-constant-list-help
(defun is-SMT-constant-list-help (constant-list)
  "is-SMT-constant-list: Check if this is a list of SMT constant declarations, the helper function"
  (if (consp constant-list)
      (if (is-SMT-constant (car constant-list))
	  (is-SMT-constant-list-help (cdr constant-list))
	nil)
    t))

;; is-SMT-constant-list
(defun is-SMT-constant-list (constant-list)
  "is-SMT-constant-list: Check if this is a list of SMT constant declarations"
  (if (not (listp constant-list))
      nil
    (is-SMT-constant-list-help constant-list)))

;; SMT-function contains functions for function declaration and definition in a SMT-formula
;; Question remained: 1. Should my functions be able to see if the formals are used in function?
;; 

(in-package "ACL2")
(include-book "SMT-expression")

;; SMT-fun-name
(defun SMT-fun-name (name)
  "SMT-fun-name: This is a SMT function name symbol"
  (if (symbolp name)
      name
    (cw "Error: This is not a valid SMT function name symbol: ~q0" name)))

;; SMT-fun-formal
(defun SMT-fun-formal (formal)
  "SMT-fun-formal: This is a SMT formal"
  (if (symbolp formal)
      formal
    (cw "Error: This is not a valid SMT formal symbol: ~q0" formal)))

;; SMT-fun-formal-list-helper
(defun SMT-fun-formal-list-helper (formal-list)
  "SMT-fun-formal-list-helper: This is a list of SMT function formals for a specific function, the helper"
  (if (consp formal-list)
      (cons (SMT-fun-formal (car formal-list)) (SMT-fun-formal-list-helper (cdr formal-list)))
    nil))

;; SMT-fun-formal-list
(defun SMT-fun-formal-list (formal-list)
  "SMT-fun-formals: This is a list of SMT function formals for a specific function"
  (if (not (listp formal-list))
      (cw "Error: Wrong formal format: ~q0" formal-list)
    (SMT-fun-formal-list-helper formal-list)))

;; SMT-function
(defun SMT-function (function)
  "SMT-function: This is a SMT function definition"
  (if (not (equal (len function) 3))
      (cw "Error: Wrong number of elements in a function definition list: ~q0" function)
    (let ((name (car function))
	  (formal (cadr function))
	  (body (caddr function)))
      (list (SMT-fun-name name)
	    (SMT-fun-formal-list formal)
	    (SMT-fun-expression body))))) 

;; SMT-function-list-help
(defun SMT-function-list-help (function-list)
  "SMT-function-list-help: This is a list of SMT function declarations, the helper"
  (if (consp function-list)
      (cons (SMT-function (car function-list)) (SMT-function-list-help (cdr function-list)))
    nil))


;; SMT-function-list
(defun SMT-function-list (function-list)
  "SMT-function-list: This is a list of SMT function declarations"
  (if (not (listp function-list))
      (cw "Error: The SMT function list is not of the right form: ~q0" function-list)
    (SMT-function-list-help function-list)))

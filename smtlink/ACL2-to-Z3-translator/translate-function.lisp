;; translate-function-list contains functions for translating a list of SMT function definitions into Z3 code
(in-package "ACL2")
(include-book "translate-expression")

;; translate-func-name
(defun translate-func-name (name)
  "translate-func-name: translate a function name"
  name)

;; translate-func-formal
(defun translate-func-formal (formal)
  "translate-func-formal: translate a formal of a function"
  formal)

;; translate-func-formal-list
(defun translate-func-formal-list (formal-list)
  "translate-func-formal-list: translate a function formal list"
  (if (consp (cdr formal-list))
      (cons (translate-func-formal (car formal-list))
	    (cons '\, (translate-func-formal-list (cdr formal-list))))
    formal-list))


;; translate-function
(defun translate-function (func)
  "translate-function: translate a function definition into a Z3 function defintion"
  (let ((name (car func))
	(formal (cadr func))
	(body (caddr func)))
    (list "def" #\Space
	  (translate-func-name name)
	  '\( (translate-func-formal-list formal) '\)
	  '\: #\Space
	  "return" #\Space
	  (translate-expression body))))

;; translate-funciton-list
(defun translate-function-list (func-list)
  "translate-function-list: translates a list of function definitions into Z3 function definitions"
  (if (consp func-list)
      (cons (translate-function (car func-list)) 
	    (cons #\Newline (translate-function-list (cdr func-list))))
    nil))

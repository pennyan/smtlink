;; SMT-formula contains functions for constructing a SMT formula in ACL2
(in-package "ACL2")
(include-book "helper")

;; -------------- SMT-operator  -----------:
(defun operator-list (opr uninterpreted)
  "operator-list: an associate list with possible SMT operators"
  (assoc opr (combine '((binary-+ binary-+ 0)
                        (binary-- binary-- 2)
                        (binary-* binary-* 0)
                        (unary-/ unary-/ 1)
                        (unary-- unary-- 1)
                        (equal equal 2)
                        (> > 2)
                        (>= >= 2)
                        (< < 2)
                        (<= <= 2)
                        (if if 3)
                        (not not 1)
                        (lambda lambda 2)
                        (implies implies 2)
                        (integerp integerp 1)
                        (rationalp rationalp 1)
                        (booleanp booleanp 1))
                      uninterpreted)
         ))

(defun is-SMT-operator (opr uninterpreted)
  "is-SMT-operator: given an operator in ACL2 format, check if it's valid"
    (if (equal (operator-list opr uninterpreted) nil)
	nil
      t))

;; SMT-operator
(defun SMT-operator (opr uninterpreted)
  "SMT-operator: given an operator in ACL2 format, establish its ACL2 format by looking up the associated list"
  (if (is-SMT-operator opr uninterpreted)
      (cadr (operator-list opr uninterpreted))
    (prog2$ (cw "Error(formula): Operator ~q0 does not exist!" opr)
	    nil)))

;; --------------------- SMT-type -------------------------:

;; is-SMT-type
(defun is-SMT-type (type)
  "SMT-type: given a type in ACL2 format, check if it's valid"
    (if (or (equal type 'RATIONALP)
	    (equal type 'INTEGERP)
	    (equal type 'BOOLEANP))
	t
      nil))

;; SMT-type
(defun SMT-type (type)
  "SMT-type: given a type in ACL2 format, establish its ACL2 format by looking up the associated list"
  (if (is-SMT-type type)
      type
    (prog2$ (cw "Error(formula): Type ~q0 not supported!" type)
	    nil)))

;; --------------------- SMT-number -------------------------:

;; is-SMT-rational
(defun is-SMT-rational (number)
  "is-SMT-rational: Check if this is a SMT rational number"
  (if (and (rationalp number)
	   (not (integerp number)))
      t
    nil))

;; is-SMT-integer
(defun is-SMT-integer (number)
  "is-SMT-integer: Check if this is a SMT integer number"
  (if (integerp number)
      t
    nil))

;; is-SMT-number
(defun is-SMT-number (number)
  "is-SMT-number: Check if this is a SMT number"
  (if (or (is-SMT-rational number)
	  (is-SMT-integer number))
      t
    nil))

;; SMT-number
(defun SMT-number (number)
  "SMT-number: This is a SMT number"
  (if (is-SMT-number number)
      number
    (cw "Error(formula): This is not a valid SMT number: ~q0" number)))

;; --------------------- SMT-variable -------------------------:
;; Q: I want to add a check on possible SMT-variables.

;; is-SMT-variable
(defun is-SMT-variable (var)
  "is-SMT-variable: check if a variable is a SMT var"
  (if (symbolp var) t nil))

;; SMT-variable
(defun SMT-variable (var)
  "SMT-variable: This is a SMT variable name"
  (if (is-SMT-variable var)
      var
    (cw "Error(formula): This is not a valid SMT variable name: ~q0" var)))

;; --------------------- SMT-constant -------------------------:

;; is-SMT-constant-name
(defun is-SMT-constant-name (name)
  "is-SMT-constant-name: Check if this is a SMT constant name"
  (if (symbolp name) t nil))

;; SMT-constant-name
(defun SMT-constant-name (name)
  "SMT-constant-name: This is a SMT constant name"
  (if (is-SMT-constant-name name)
      name
    (cw "Error(formula): This is not a valid SMT constant name: ~q0" name)))

;; SMT-constant
(defun SMT-constant (constant)
  "SMT-constant: This is a SMT constant declaration"
  (if (not (equal (len constant) 2))
      (cw "Error(formula): Wrong number of elements in a constant declaration list: ~q0" constant)
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
      (cw "Error(formula): The SMT constant list is not in the right form: ~q0" constant-list)
    (SMT-constant-list-help constant-list)))

;; --------------------- SMT-declaration -------------------------:

;; SMT-declaration 
(defun SMT-declaration (decl)
  "SMT-declaration: This is a SMT variable declaration"
  (if (not (equal (len decl) 2))
      (cw "Error(formula): Wrong number of elements in a variable declaration list: ~q0" decl)
    (let ((type (car decl))
	  (name (cadr decl)))
      (list (SMT-type type) (SMT-variable name)))))

;; SMT-declaration-list-help
(defun SMT-declaration-list-help (decl-list)
  "SMT-declaration-list-help: This is a list of SMT variable declarations, the helper function"
  (if (consp decl-list)
      (cond ((equal (car decl-list) 'if)
	     (cons (SMT-declaration (cadr decl-list))
		   (SMT-declaration-list-help (caddr decl-list))))
	    (t (cons (SMT-declaration decl-list)
		     nil)))
    nil))

;; SMT-declaration-list
(defun SMT-declaration-list (decl-list)
  "SMT-decl-list: This is a list of SMT variable declarations"
  (if (not (listp decl-list))
      (cw "Error(formula): The SMT declaration list is not in the right form: ~q0" decl-list)
    (SMT-declaration-list-help decl-list)))

;; --------------------- SMT-expression -------------------------:

(mutual-recursion

;; SMT-lambda-formal
(defun SMT-lambda-formal (formal)
  "SMT-lambda-formal: check if it's a valid formal list for a lambda expression"
  (if (endp formal)
      nil
    (if (symbolp (car formal))
	(cons (car formal)
	      (SMT-lambda-formal (cdr formal)))
      (cw "Error(formula): not a valid symbol in a formal list ~q0" (car formal)))))

;; SMT-expression-long
(defun SMT-expression-long (expression uninterpreted)
  "SMT-expression-long: recognize a SMT expression, in a SMT expression's parameters"
  (if (consp expression)
      (cons (SMT-expression (car expression) uninterpreted)
	    (SMT-expression-long (cdr expression) uninterpreted))
    nil))

;; SMT-expression
(defun SMT-expression (expression uninterpreted)
  "SMT-expression: a SMT expression in ACL2"
  (if (consp expression)
      (cond ((and (consp (car expression))
		  (is-SMT-operator (caar expression) uninterpreted)
		  (equal (caar expression) 'lambda))
	     (cons (list (SMT-operator
			  (car (car expression)) uninterpreted)
			 (SMT-lambda-formal
			  (cadr (car expression)))
			 (SMT-expression
			  (caddr (car expression)) uninterpreted))
		   (SMT-expression-long (cdr expression) uninterpreted)))
	    ((is-SMT-operator (car expression) uninterpreted)
	     (cons (SMT-operator (car expression) uninterpreted)
		   (SMT-expression-long (cdr expression) uninterpreted)))
	    ; mrg: added support for quoted symbols, 21 May 2015
	    ;; for handling a list and atoms
	    ( (equal (car expression) 'QUOTE)
	      (let ( (quoted-expr (cadr expression)))
		     (cond ( (consp quoted-expr) ; it's a quoted list
			     (cons 'list (SMT-expression-long quoted-expr uninterpreted)) )
			   ( (and quoted-expr (symbolp quoted-expr)) expression ) ; mrg leave quoted symbols untouched
		           ( t (SMT-expression (cadr expression) uninterpreted) ))) )
	    (t (cw "Error(formula): This is not a valid operator: ~q0" expression)))
    (cond ((is-SMT-number expression) (SMT-number expression))
	  ((is-SMT-variable expression) (SMT-variable expression))
	  (t (cw "Error(formula): Invalid number or variable: ~q0" expression)))))
)

;; --------------------- SMT-hypothesis -------------------------:

;; SMT-hypothesis-list
(defun SMT-hypothesis-list (hyp-list uninterpreted)
  "SMT-hypothesis-list: This is a SMT hypothesis list"
  (if (not (listp hyp-list))
      (cw "Error(formula): The SMT hypothesis list is not in the right form: ~q0" hyp-list)
    (SMT-expression hyp-list uninterpreted)))

;; --------------------- SMT-conclusion -------------------------:

;; SMT-conclusion-list
(defun SMT-conclusion-list (concl-list uninterpreted)
  "SMT-conclusion-list: This is a SMT conclusion list"
  (if (not (listp concl-list))
      (cw "Error(formula): The SMT conclusion list is not in the right form: ~q0" concl-list)
    (SMT-expression concl-list uninterpreted)))
;; --------------------- SMT-formula ----------------------------:

;; SMT-formula
(defun SMT-formula (const-list
		    decl-list
		    hyp-list
		    concl-list
        uninterpreted)
  "SMT-formula: This is a SMT formula"
  (list (SMT-constant-list const-list)
	(SMT-declaration-list decl-list)
	(SMT-hypothesis-list hyp-list uninterpreted)
	(SMT-conclusion-list concl-list uninterpreted))
  )

;; SMT-formula-top
(defmacro SMT-formula-top (&key const-list
				decl-list
				hyp-list
				concl-list
        uninterpreted)
  "SMT-formula-top: This is a macro for fetching parameters of a SMT formula"
  (list 'quote (SMT-formula const-list
			    decl-list 
			    hyp-list 
			    concl-list
          uninterpreted))
  )
;; SMT-formula contains functions for constructing a SMT formula in ACL2
(in-package "ACL2")

;; -------------- SMT-operator  -----------:
(defun operator-list (opr)
  "operator-list: an associate list with possible SMT operators"
  (assoc opr '((binary-+ binary-+ 0)
	       (binary-- binary-- 2)
	       (binary-* binary-* 0)
	       (unary-/ unary-/ 1)
	       (equal equal 2)
	       (> > 2)
	       (>= >= 2)
	       (< < 2)
	       (<= <= 2)
	       (if if 3)
	       (not not 1)
	       (let let 2))))

(defun is-SMT-operator (opr)
  "is-SMT-operator: given an operator in ACL2 format, check if it's valid"
    (if (equal (operator-list opr) nil)
	nil
      t))

;; SMT-operator
(defun SMT-operator (opr)
  "SMT-operator: given an operator in ACL2 format, establish its ACL2 format by looking up the associated list"
  (if (is-SMT-operator opr)
      (cadr (operator-list opr))
    (prog2$ (cw "Error: Operator ~q0 does not exist!" opr)
	    nil)))

;; --------------------- SMT-type -------------------------:

;; is-SMT-type
(defun is-SMT-type (type)
  "SMT-type: given a type in ACL2 format, check if it's valid"
    (if (or (equal type 'RATIONALP)
	    (equal type 'INTEGERP))
	t
      nil))

;; SMT-type
(defun SMT-type (type)
  "SMT-type: given a type in ACL2 format, establish its ACL2 format by looking up the associated list"
  (if (is-SMT-type type)
      type
    (prog2$ (cw "Error: Type ~q0 not supported!" type)
	    nil)))

;; --------------------- SMT-number -------------------------:

;; is-SMT-number
(defun is-SMT-number (number)
  "is-SMT-number: Check if this is a SMT number"
  (if (or (rationalp number)
	  (integerp number))
      t
    nil))

;; SMT-number
(defun SMT-number (number)
  "SMT-number: This is a SMT number"
  (if (is-SMT-number number)
      number
    (cw "Error: This is not a valid SMT number: ~q0" number)))

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
    (cw "Error: This is not a valid SMT variable name: ~q0" var)))

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

;; --------------------- SMT-declaration -------------------------:

;; SMT-declaration 
(defun SMT-declaration (decl)
  "SMT-declaration: This is a SMT variable declaration"
  (if (not (equal (len decl) 2))
      (cw "Error: Wrong number of elements in a variable declaration list: ~q0" decl)
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
      (cw "Error: The SMT declaration list is not in the right form: ~q0" decl-list)
    (SMT-declaration-list-help decl-list)))

;; --------------------- SMT-expression -------------------------:

;; SMT-let-var-list
(defun SMT-let-var-list (var-list)
  "SMT-let-var-list: recognize a list of variables of a let expression"
  (if (not (and (listp (car var-list))
		(equal (length (car var-list)) 2)))
      nil
    t))

(mutual-recursion
;; SMT-expression-long
(defun SMT-expression-long (expression)
  "SMT-expression-long: recognize a SMT expression, in a SMT expression's parameters"
  (if (consp expression)
      (cons (SMT-expression (car expression))
	    (SMT-expression-long (cdr expression)))
    nil))

;; SMT-expression
;; Right now, we don't allow functions in the formula
(defun SMT-expression (expression)
  "SMT-expression: a SMT expression in ACL2"
  (if (consp expression)
      (cond ((is-SMT-operator (car expression))
	     (if (equal (car expression) 'let)
		 (list (SMT-operator (car expression))
		       (SMT-let-var-list (cadr expression))
		       (SMT-expression (caddr expression)))
	       (cons (SMT-operator (car expression))
		     (SMT-expression-long (cdr expression)))))
	     ((equal (car expression) 'QUOTE)
	      (SMT-expression (cadr expression)))
	     (t (cw "Error: This is not a valid operator: ~q0" expression)))
    (cond ((is-SMT-number expression) (SMT-number expression))
	  ((is-SMT-variable expression) (SMT-variable expression))
	  (t (cw "Error: Invalid number or variable: ~q0" expression)))))
)

;; --------------------- SMT-hypothesis -------------------------:

;; SMT-hypothesis-list
(defun SMT-hypothesis-list (hyp-list)
  "SMT-hypothesis-list: This is a SMT hypothesis list"
  (if (not (listp hyp-list))
      (cw "Error: The SMT hypothesis list is not in the right form: ~q0" hyp-list)
    (SMT-expression hyp-list)))

;; --------------------- SMT-conclusion -------------------------:

;; SMT-conclusion-list
(defun SMT-conclusion-list (concl-list)
  "SMT-conclusion-list: This is a SMT conclusion list"
  (if (not (listp concl-list))
      (cw "Error: The SMT conclusion list is not in the right form: ~q0" concl-list)
    (SMT-expression concl-list)))
;; --------------------- SMT-formula ----------------------------:

;; SMT-formula
(defun SMT-formula (const-list
		    decl-list
		    hyp-list
		    concl-list)
  "SMT-formula: This is a SMT formula"
  (list (SMT-constant-list const-list)
	(SMT-declaration-list decl-list)
	(SMT-hypothesis-list hyp-list)
	(SMT-conclusion-list concl-list))
  )

;; SMT-formula-top
(defmacro SMT-formula-top (&key const-list
				decl-list
				hyp-list
				concl-list)
  "SMT-formula-top: This is a macro for fetching parameters of a SMT formula"
  (list 'quote (SMT-formula const-list
			    decl-list 
			    hyp-list 
			    concl-list))
  )

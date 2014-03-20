;; SMT-formula contains functions for constructing a SMT formula in ACL2
(in-package "ACL2")

;; -------------- operator associate list  -----------:
;; translate-operator-asso
(defun SMT-operator-asso (opr)
  "SMT-operator-asso: given an operator in ACL2 format, establish its ACL2 format by looking up the associated list"
  (let ((result (assoc opr '((binary-+ binary-+)
			     (binary-- binary--)
			     (binary-* binary-*)
			     (binary-/ binary-/)
			     (equal equal)
			     (> >)
			     (>= >=)
			     (< <)
			     (<= <=)
			     (if if)
			     (not not)))))
    (if (equal result nil)
	(prog2$ nil
		(cw "Operator ~q0 does not exist!" opr))
	(cadr result))))

(defun is-SMT-operator-asso (opr)
  "SMT-operator-asso: given an operator in ACL2 format, establish its ACL2 format by looking up the associated list"
    (if (not (or (equal opr 'binary-+)
		 (equal opr 'binary--)
		 (equal opr 'binary-*)
		 (equal opr 'binary-/)
		 (equal opr 'equal)
		 (equal opr '>)
		 (equal opr '<)
		 (equal opr '>=)
		 (equal opr '<=)
		 (equal opr 'if)
		 (equal opr 'not)))
	nil
      t))

;; --------------------- SMT-arithmetic -------------------------:

;; is-SMT-plus
(defun is-SMT-plus (operator)
  "is-SMT-plus: Check if it is a symbol for arithmetic plus"
  (if (equal operator 'binary-+) t nil))

;; SMT-plus
(defun SMT-plus (operator)
  "SMT-plus: the symbol for arithmetic plus"
  (if (is-SMT-plus operator)
      operator
    (cw "Error: This is not a valid plus operator: ~q0" operator)))

;; is-SMT-minus
(defun is-SMT-minus (operator)
  "is-SMT-minus: Check if it is a symbol for arithmetic minus"
  (if (equal operator 'binary--) t nil))

;; SMT-minus
(defun SMT-minus (operator)
  "SMT-minus: the symbol for arithmetic minus"
  (if (is-SMT-minus operator)
      operator
    (cw "Error: This is not a valid minus operator: ~q0" operator)))

;; is-SMT-multiply
(defun is-SMT-multiply (operator)
  "is-SMT-multiply: Check if it is a symbol for arithmetic multiply"
  (if (equal operator 'binary-*) t nil))

;; SMT-multiply
(defun SMT-multiply (operator)
  "SMT-multiply: the symbol for arithmetic multiply"
  (if (is-SMT-multiply operator)
      operator
     (cw "Error: This is not a valid multiply operator: ~q0" operator)))

;; is-SMT-divide
(defun is-SMT-divide (operator)
  "is-SMT-divide: Check if it is a symbol for arithmetic divide"
  (if (equal operator 'binary-/) t nil))

;; SMT-divide
(defun SMT-divide (operator)
  "SMT-divide: the symbol for arithmetic divide"
  (if (is-SMT-divide operator)
      operator
    (cw "Error: This is not a valid divide operator: ~q0" operator)))

;; is-SMT-arithmetic
(defun is-SMT-arithmetic (operator)
  "is-SMT-arithmetic: Check if it is a symbols for arithmetic operators"
  (cond ((is-SMT-plus operator) t)
	((is-SMT-minus operator) t)
	((is-SMT-multiply operator) t)
	((is-SMT-divide operator) t)
	(t nil)))

;; SMT-arithmetic
(defun SMT-arithmetic (operator)
  "SMT-arithmetic: the symbols for arithmetic operators"
  (cond ((is-SMT-plus operator) (SMT-plus operator))
	((is-SMT-minus operator) (SMT-minus operator))
	((is-SMT-multiply operator) (SMT-multiply operator))
	((is-SMT-divide operator) (SMT-divide operator))
	(t (cw "Error: There exists no such arithmetic operator in SMT-formula: ~q0" operator))))

;; --------------------- SMT-comparison -------------------------:

;; is-SMT-equal
(defun is-SMT-equal (operator)
  "is-SMT-equal: Check if this is the comparison symbol for equal"
  (if (equal operator 'equal) t nil))

;; SMT-equal
(defun SMT-equal (operator)
  "SMT-equal: This is the comparison symbol for equal"
  (if (is-SMT-equal operator)
      operator
    (cw "Error: This is not a valid equal-to operator: ~q0" operator)))

;; is-SMT-greater-than
(defun is-SMT-greater-than (operator)
  "is-SMT-greater-than: Check if this is the comparison symbol for >"
  (if (equal operator '>) t nil))

;; SMT-greater-than
(defun SMT-greater-than (operator)
  "SMT-greater-than: This is the comparison symbol for >"
  (if (is-SMT-greater-than operator)
      operator
    (cw "Error: This is not a valid greater-than operator: ~q0" operator)))

;; is-SMT-greater-equal
(defun is-SMT-greater-equal (operator)
  "is-SMT-greater-equal: Check if this is the comparison symbol for >="
  (if (equal operator '>=) t nil))

;; SMT-greater-equal
(defun SMT-greater-equal (operator)
  "SMT-greatere-equal: This is the comparison symbol for >="
  (if (is-SMT-greater-equal operator)
      operator
    (cw "Error: This is not a valid greater-or-equal-to operator: ~q0" operator)))

;; is-SMT-smaller-than
(defun is-SMT-smaller-than (operator)
  "is-SMT-smaller-than: Check if this is the comparison symbol for <"
  (if (equal operator '<) t nil))

;; SMT-smaller-than
(defun SMT-smaller-than (operator)
  "SMT-smaller-than: This is the comparison symbol for <"
  (if (is-SMT-smaller-than operator)
      operator
    (cw "Error: This is not a valid smaller-than operator: ~q0" operator)))

;; is-SMT-smaller-equal
(defun is-SMT-smaller-equal (operator)
  "is-SMT-smaller-equal: Check if this is the comparison symbol for <="
  (if (equal operator '<=) t nil))

;; SMT-smaller-equal
(defun SMT-smaller-equal (operator)
  "SMT-smaller-equal: This is the comparison symbol for <="
  (if (is-SMT-smaller-equal operator)
      operator
    (cw "Error: This is not a valid smaller-or-equal-to operator: ~q0" operator)))

;; is-SMT-comparison
(defun is-SMT-comparison (operator)
  "is-SMT-comparison: Check if this is a SMT comparison operator symbol"
  (cond ((is-SMT-equal operator) t) 
	((is-SMT-greater-than operator) t)
	((is-SMT-greater-equal operator) t)
	((is-SMT-smaller-than operator) t)
	((is-SMT-smaller-equal operator) t)
	(t nil)))

;; SMT-comparison
(defun SMT-comparison (operator)
  "SMT-comparison: defines SMT comparison operator symbols"
  (cond ((is-SMT-equal operator) (SMT-equal operator)) 
	((is-SMT-greater-than operator) (SMT-greater-than operator))
	((is-SMT-greater-equal operator) (SMT-greater-equal operator))
	((is-SMT-smaller-than operator) (SMT-smaller-than operator))
	((is-SMT-smaller-equal operator) (SMT-smaller-equal operator))
	(t (cw "Error: There exists no such comparison operator in SMT-formula: ~q0" operator))))

;; --------------------- SMT-logic -------------------------:

;; is-SMT-and
(defun is-SMT-and (operator)
  "is-SMT-and: Check if this is the logic symbol for and"
  (if (equal operator 'and) t nil))

;; SMT-and
(defun SMT-and (operator)
  "SMT-and: This is the logic symbol for and"
  (if (is-SMT-and operator)
      operator
    (cw "Error: This is not a valid and operator: ~q0" operator)))

;; is-SMT-or
(defun is-SMT-or (operator)
  "is-SMT-or: Check if this is the logic symbol for or"
  (if (equal operator 'or) t nil))

;; SMT-or
(defun SMT-or (operator)
  "SMT-or: This is the logic symbol for or"
  (if (is-SMT-or operator)
      operator
    (cw "Error: This is not a valid or operator: ~q0" operator)))

;; is-SMT-not
(defun is-SMT-not (operator)
  "is-SMT-not: Check if this is the logic symbol for not"
  (if (equal operator 'not) t nil))

;; SMT-not
(defun SMT-not (operator)
  "SMT-not: This is the logic symbol for not"
  (if (is-SMT-not operator)
      operator
    (cw "Error: This is not a valid not operator: ~q0" operator)))

;; is-SMT-logic
(defun is-SMT-logic (operator)
  "is-SMT-logic: check if this is a SMT boolean logic operator symbol"
  (cond ((is-SMT-and operator) t)
	((is-SMT-or operator) t)
	((is-SMT-not operator) t)
	(t nil)))

;; SMT-logic
(defun SMT-logic (operator)
  "SMT-logic: defines SMT boolean logic operator symbols"
  (cond ((is-SMT-and operator) (SMT-and operator))
	((is-SMT-or operator) (SMT-or operator))
	((is-SMT-not operator) (SMT-not operator))
	(t (cw "Error: There exists no such boolean logic operator in SMT-formula: ~q0" operator))))

;; --------------------- SMT-type -------------------------:

;; is-SMT-real
(defun is-SMT-real (type)
  "is-SMT-real: Check if this is a real declaration symbol. Only rationalp is accepted because ACL2-NUMBERP and COMPLEX-RATIONALP contains rational numbers that probably cannot be handled by Z3. If I state them as reals in Z3, even if Z3 proves the theorem, I can't say so because complex numbers are not considered."
  (cond ((equal type 'RATIONALP) t)
	(t nil)))

;; SMT-real
(defun SMT-real (type)
  "SMT-real: real declaration symbols"
  (cond ((is-SMT-real type) type)
	(t (cw "Error: Input is not a valid real symbol: ~q0" type))))

;; is-SMT-integer
(defun is-SMT-integer (type)
  "is-SMT-integer: Check if this is an integer declaration symbol"
  (if (equal type 'INTEGERP) t nil))

;; SMT-integer
(defun SMT-integer (type)
  "SMT-integer: integer declaration symbols"
  (if (is-SMT-integer type)
      type
    (cw "Error: Input is not a valid integer symbol: ~q0" type)))

;; is-SMT-type: type declaration symbols
(defun is-SMT-type (type)
  "is-SMT-type: Check if this is a type declaration symbol"
  (cond ((is-SMT-real type) t)
	((is-SMT-integer type) t)
	(t nil)))

;; SMT-type: type declaration symbols
(defun SMT-type (type)
  "SMT-type: type declaration symbols"
  (cond ((is-SMT-real type) (SMT-real type))
	((is-SMT-integer type) (SMT-integer type))
	(t (cw "Error: There exist no such type in ACL2: ~q0" type))))

;; --------------------- SMT-number -------------------------:

;; is-SMT-number
(defun is-SMT-number (number)
  "is-SMT-number: Check if this is a SMT number"
  (if (or (rationalp number) (integerp number)) t nil))

;; SMT-number
(defun SMT-number (number)
  "SMT-number: This is a SMT number"
  (if (is-SMT-number number)
      number
    (cw "Error: This is not a valid SMT number: ~q0" number)))

;; --------------------- SMT-variable -------------------------:

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

;; --------------------- SMT-operator -------------------------:

;; is-SMT-operator
(defun is-SMT-operator (opr)
  "is-SMT-operator: check if this is a SMT operator"
  (if (or (is-SMT-arithmetic opr) 
	  (is-SMT-logic opr) 
	  (is-SMT-comparison opr))
      t
    nil))

;; SMT-operator
(defun SMT-operator (opr)
  "SMT-operator: construct a SMT operator"
  (cond ((is-SMT-arithmetic opr) (SMT-arithmetic opr))
	((is-SMT-logic opr) (SMT-logic opr))
	((is-SMT-comparison opr) (SMT-comparison opr))
	(t (cw "Error: This is not a valid operator: ~q0" opr))))

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

(mutual-recursion
;; SMT-expression-long
(defun SMT-expression-long (expression)
  "SMT-expression-long: recognize a SMT expression, in a SMT expression's parameters"
  (if (consp expression)
      (cons (SMT-expression (car expression))
	    (SMT-expression-long (cdr expression)))
    nil))

;; SMT-expression
(defun SMT-expression (expression)
  "SMT-expression: a SMT expression in ACL2"
  (if (consp expression)
      (cond ((is-SMT-operator-asso (car expression)) 
	     (cons (SMT-operator-asso (car expression))
		   (SMT-expression-long (cdr expression))))
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

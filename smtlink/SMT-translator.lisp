;; translate-SMT-formula translate a SMT formula in ACL2 into Z3 python code
(in-package "ACL2")
(include-book "SMT-formula")

;; -------------- translate operator  -----------:

;; translate-operator-list
(defun translate-operator-list (opr)
  "translate-operator-list: look up an associate list for the translation"
  (assoc opr '((binary-+ "s.plus" 0)
	      (binary-- "s.minus" 2)
	      (binary-* "s.times" 0)
	      (unary-/ "s.reciprocal" 1)
	      (unary-- "s.negate" 1)
	      (equal "s.equal" 2)
	      (> "s.gt" 2)
	      (>= "s.ge" 2)
	      (< "s.lt" 2)
	      (<= "s.le" 2)
	      (if "s.ifx" 3)
	      (not "s.notx" 1)
	      (let "s.let" 2))))

;; translate-operator
(defun translate-operator (opr)
  "translate-operator: given an operator in ACL2 format, translate into its Z3 format by looking up the associated list"
  (let ((result (translate-operator-list opr)))
    (if (equal result nil)
	(prog2$ (cw "Error: Operator ~q0 does not exist!" opr)
		nil)
      (cadr result))))

;; ----------------------- translate-type -----------------------------:

;; translate-type-list
(defun translate-type-list (type)
  "translate-type-list: look up an associate list for the translation"
  (assoc type '((RATIONALP "s.isReal")
	       (INTEGERP "s.isReal"))))

;; translate-type
(defun translate-type (type)
  "translate-type: translates a type in ACL2 SMT-formula into Z3 type"     ;; all using reals because Z3 is not very good at mixed types
  (let ((result (translate-type-list type)))
    (if (equal result nil)
	(prog2$ (cw "Error: Type ~q0 does not exist!" opr)
		nil)
      (cadr result))))

;; ----------------------- translate-number -----------------------------:

;; translate-number
(defun translate-number (num)
  "translate-number: translates ACL2 SMT-number into a Z3 number"
  (if (is-SMT-number num)
      num
    (cw "Error: Cannot translate an unrecognized number: ~q0" num)))

;; ----------------------- translate-variable ---------------------------:

;; translate-variable
(defun translate-variable (var)
  "translate-variable: transalte a SMT variable into Z3 variable"
  (if (is-SMT-variable var)
      (list "s.getVar('" var "')")
    (cw "Error: Cannot translate an unrecognized variable: ~q0" var)))

;; ----------------------- translate-constant ---------------------------:

;; translate-const-name 
(defun translate-const-name (const-name)
  "translate-const-name: translate a SMT constant name into Z3"
  const-name)

;; translate-constant
(defun translate-constant (const)
  "translate-constant: translate a SMT constant definition into Z3 code"
  (list (translate-const-name (car const)) '= (translate-number (cadr const))))

;; translate-constant-list
(defun translate-constant-list (const-list)
  "translate-constant-list: translate a SMT constant list in ACL2 into a Z3 line of code"
  (if (consp const-list)
      (cons (translate-constant (car const-list)) 
	    (cons #\Newline (translate-constant-list (cdr const-list))))
    nil))

;; ----------------------- translate-declaration ---------------------------:

;; translate-declaration
(defun translate-declaration (decl)
  "translate-declaration: translate a declaration in ACL2 SMT formula into Z3 declaration"
  (let ((type (car decl))
	(name (cadr decl)))
    (list (translate-type type) "(\"" name "\")")))

;; translate-declaration-list
(defun translate-declaration-list (decl-list)
  "translate-declaration-list: translate a list of SMT-formula declarations into Z3 code"
  (if (consp decl-list)
      (cons (translate-declaration (car decl-list))
	    (cons #\Newline (translate-declaration-list (cdr decl-list))))
    nil))

;; ----------------------- translate-expression --------------------------:
(mutual-recursion
;; make-let-list-elem
(defun make-let-list-elem (let-list-elem)
  "make-let-list-elem: translating one element of a let binding list"
  (if (symbolp (car let-list-elem))
      (list "['" (car let-list-elem) "',"
	    (translate-expression (cadr let-list-elem)) "]")
    (cw "Error: first element ~q0 of a let binding expression should be a symbol!" (car let-list-elem))))

;; make-let-list
(defun make-let-list (let-list)
  "make-let-list: translating the binding list of a let expression"
  (if (endp (cdr let-list))
      (list "["
	    (make-let-list-elem (car let-list))
	    "]")
    (list "["
	  (cons (make-let-list-elem (car let-list))
		(cons '\, (make-let-list (cdr let-list))))
	  "]")))

;; translate-expression-long
(defun translate-expression-long (expression)
  "translate-expression-long: translate a SMT expression's parameters in ACL2 into Z3 expression"
  (if (consp expression)
      (cons (translate-expression (car expression))
	    (if (consp (cdr expression))
		(cons '\, (translate-expression-long (cdr expression)))
	      nil))
    nil))

;; stuff.let(['x', 2.0], ['y', v('a')*v('b') + v('c')], ['z', ...]).inn(2*v('x') - v('y'))
;; translate-expression
(defun translate-expression (expression)
  "translate-expression: translate a SMT expression in ACL2 to Z3 expression"
  (if (and (not (equal expression 'nil))
	   (consp expression))
      (cond ((and (is-SMT-operator (car expression))
		  ;; special treatment for let expression
		  (equal (car expression) 'let))
	     (list (translate-operator (car expression))
		   '\(
		   (make-let-list (cadr expression))
		   '\). "inn" '\(
		   (translate-expression (caddr expression))
		   '\) ))
	    ((is-SMT-operator (car expression)) 
	     (list (translate-operator (car expression))
		   '\(
		   (translate-expression-long (cdr expression))
		   '\)))
	    ;; want to use unknown function instead of error message
	    (t (list "s.unknown" '\( (translate-expression-long (cdr expression)) '\))))
    (cond ((is-SMT-number expression) (translate-number expression))
	  ((equal expression 'nil) "False")
	  ((equal expression 't) "True")
	  ((is-SMT-variable expression) (translate-variable expression))
	  (t (cw "Error: Invalid number or variable: ~q0" expression)))))
)

;; ----------------------- translate-hypothesis --------------------------:

;; translate-hypothesis-list
(defun translate-hypothesis-list (hyp-list)
  "translate-hypothesis-list: translate a SMT-formula hypothesis statement into Z3"
  (list (cons "hypothesis" 
	      (cons '= (translate-expression hyp-list))) #\Newline))

;; ----------------------- translate-conclusion --------------------------:
;; translate-conclusion-list
(defun translate-conclusion-list (concl-list)
  "translate-conclusion-list: translate a SMT-formula conclusion statement into Z3"
  (list (cons "conclusion" 
	      (cons '= (translate-expression concl-list))) #\Newline))

;; ----------------------- translate-theorem --------------------------:
;; translate-theorem
(defun translate-theorem ()
  "translate-theorem: construct a theorem statement for Z3"
  (list "s.prove(hypothesis, conclusion)" #\Newline))

;; ----------------------- translate-SMT-formula --------------------------:

;; translate-SMT-formula
(defun translate-SMT-formula (formula)
  "translate-SMT-formula: translate a SMT formula into its Z3 code"
  (let ((const-list (car formula))
	(decl-list (cadr formula))
	(hypo-list (caddr formula))
	(concl-list (cadddr formula)))
    (list (translate-constant-list const-list)
	  (translate-declaration-list decl-list)
	  (translate-hypothesis-list hypo-list)
	  (translate-conclusion-list concl-list)
	  (translate-theorem))))

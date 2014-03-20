;; translate-SMT-formula translate a SMT formula in ACL2 into Z3 python code
(in-package "ACL2")
(include-book "SMT-formula")

;; -------------- operator associate list  -----------:
;; translate-operator-asso
(defun translate-operator-asso (opr)
  "translate-operator-asso: given an operator in ACL2 format, translate into its Z3 format by looking up the associated list"
  (let ((result (assoc opr '((binary-+ "acl2_plus")
			     (binary-- "acl2_minus")
			     (binary-* "acl2_multiply")
			     (binary-/ "acl2_divide")
			     (equal "acl2_equal")
			     (> "acl2_gt")
			     (>= "acl2_ge")
			     (< "acl2_lt")
			     (<= "acl2_le")
			     (if "acl2_if")))))
    (if (equal result nil)
	(prog2$ nil
		(cw "Operator ~q0 does not exist!" opr))
	(cadr result))))
  
;; ---------------------- translate-arithmetic -----------------------:

;; translate-plus 
(defun translate-plus ()
  "translate-plus: translate a plus operator into Z3 function"
  "acl2_plus")

;; translate-minus 
(defun translate-minus ()
  "translate-minus: translate a minus operator into Z3 function"
  "acl2_minus")

;; translate-multiply
(defun translate-multiply ()
  "translate-multiply: translate a multiply operator into Z3 function"
  "acl2_multiply")

;; translate-divide
(defun translate-divide ()
  "translate-divide: translate a divide operator into Z3 function"
  "acl2_divide")

;; translate-arithmetic
(defun translate-arithmetic (operator)
  "translate-arithmetic: translates an arithmetic operator in a SMT-formula of ACL2 into Z3"
  (cond ((is-SMT-plus operator) (translate-plus))
	((is-SMT-minus operator) (translate-minus))
	((is-SMT-multiply operator) (translate-multiply))
	((is-SMT-divide operator) (translate-divide))
	(t (cw "Error: Can not translate unrecognized operator: ~q0" operator))))

;; ---------------------- translate-comparison -----------------------:
;; translate-equal 
(defun translate-equal ()
  "translate-equal: translate equal operator in SMT-formula into Z3"
  "acl2_equal")

;; translate-greater-than
(defun translate-greater-than ()
  "translate-greater-than: translate greater than operator in SMT-formula into Z3"
  "acl2_gt")

;; translate-greater-equal 
(defun translate-greater-equal ()
  "translate-greater-equal: translate greater-or-equal-to operator in SMT-formula into Z3"
  "acl2_get")

;; translate-smaller-than
(defun translate-smaller-than ()
  "translate-smaller-than: translate smaller-than operator in SMT-formula into Z3"
  "acl2_st")

;; translate-smaller-equal
(defun translate-smaller-equal ()
  "translate-smaller-equal: translate smaller-or-equal-to operator in SMT-formula into Z3"
  "acl2_set")

;; transalate-comparison
(defun translate-comparison (operator)
  "translate-comparison: translate comparison operators in SMT-formula into Z3"
  (cond ((is-SMT-equal operator) (translate-equal))
	((is-SMT-greater-than operator) (translate-greater-than))
	((is-SMT-greater-equal operator) (translate-greater-equal))
	((is-SMT-smaller-than operator) (translate-smaller-than))
	((is-SMT-smaller-equal operator) (translate-smaller-equal))
	(t (cw "Error: Can not translate unrecognized operator: ~q0" operator))))

;; ----------------------- translate-logic -----------------------------:

;; translate-and
(defun translate-and ()
  "translate-and: translate an and operator in SMT-formula into Z3"
  "acl2_and")

;; translate-or
(defun translate-or ()
  "translate-or: translate an or operator in SMT-formula into Z3"
  "acl2_or")

;; translate-not
(defun translate-not ()
  "translate-not: translate a not operator in SMT-formula into Z3"
  "acl2_not")

;; translate-logic
(defun translate-logic (operator)
  "translate-logic: translate a logic operator in SMT-formula into Z3"
  (cond ((is-SMT-and operator) (translate-and))
	((is-SMT-or  operator) (translate-or))
	((is-SMT-not operator) (translate-not))
	(t (cw "Error: Can not translate unrecognized operator: ~q0" operator))))

;; ----------------------- translate-type -----------------------------:

;; translate-real
(defun translate-real ()
  "translate-real: translate into real type in Z3"
  "Real")

;; translate-integer
(defun translate-integer ()
  "translate-integer: translate into integer type in Z3"
  "Int")

;; translate-type
(defun translate-type (type)
  "translate-type: translates a type in ACL2 SMT-formula into Z3 type"     ;; all using reals because Z3 is not very good at mixed types
  (cond ((is-SMT-real type)
	 (translate-real))
	(t (translate-real))))
     ;; integer case
     ;; (t (translate-integer type))

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
      var
    (cw "Error: Cannot translate an unrecognized variable: ~q0" var)))

;; ----------------------- translate-operator ---------------------------:

;; translate-operator
(defun translate-operator (opr)
  "translate-operator: translate a SMT operator into Z3 operator"
  (cond ((is-SMT-arithmetic opr) (translate-arithmetic opr))
	((is-SMT-logic opr) (translate-logic opr))
	((is-SMT-comparison opr) (translate-comparison opr))
	(t (cw "Error: Cannot translate unrecognized operator: ~q0" opr))))

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
    (list (translate-variable name) '= (translate-type type) '\(  '\" (translate-variable name) '\" '\))))

;; translate-declaration-list
(defun translate-declaration-list (decl-list)
  "translate-declaration-list: translate a list of SMT-formula declarations into Z3 code"
  (if (consp decl-list)
      (cons (translate-declaration (car decl-list))
	    (cons #\Newline (translate-declaration-list (cdr decl-list))))
    nil))

;; ----------------------- translate-expression --------------------------:
(mutual-recursion
;; translate-expression-long
(defun translate-expression-long (expression)
  "translate-expression-long: translate a SMT expression's parameters in ACL2 into Z3 expression"
  (if (consp expression)
      (cons (translate-expression (car expression))
	    (if (consp (cdr expression))
		(cons '\, (translate-expression-long (cdr expression)))
	      nil))
    nil))

;; translate-expression
(defun translate-expression (expression)
  "translate-expression: translate a SMT expression in ACL2 to Z3 expression"
  (if (and (not (equal expression 'nil))
	   (consp expression))
      (cond ((is-SMT-operator-asso (car expression)) 
	     (list (translate-operator-asso (car expression))
		   '\(
		   (translate-expression-long (cdr expression))
		   '\)))
	    (t (cw "Error: This is not a valid function: ~q0" (car expression))))
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
  (list "prove(Implies(And(hypothesis,if_constraint_bool), conclusion))" #\Newline))

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

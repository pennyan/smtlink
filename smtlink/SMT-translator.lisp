;; translate-SMT-formula translate a SMT formula in ACL2 into Z3 python code
(in-package "ACL2")
(include-book "SMT-formula")
(include-book "helper")

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
	       (lambda "lambda" 2)
	       (nth "s.nth" 2)
	       (list "s.array" 0)
	       (implies "s.implies" 2)
	       (integerp "s.integerp" 1)
	       (rationalp "s.rationalp" 1)
	       (booleanp "s.booleanp" 1))))

;; translate-operator
(defun translate-operator (opr)
  "translate-operator: given an operator in ACL2 format, translate into its Z3 format by looking up the associated list"
  (let ((result (translate-operator-list opr)))
    (if (equal result nil)
	(prog2$ (cw "Error(translator): Operator ~q0 does not exist!" opr)
		nil)
      (cadr result))))

;; ----------------------- translate-type -----------------------------:

;; translate-type-list
(defun translate-type-list (type)
  "translate-type-list: look up an associate list for the translation"
  (assoc type '((RATIONALP "s.isReal")
		(INTEGERP "s.isReal")
		(BOOLEANP "s.isBool"))))

;; translate-type
(defun translate-type (type)
  "translate-type: translates a type in ACL2 SMT-formula into Z3 type"     ;; all using reals because Z3 is not very good at mixed types
  (let ((result (translate-type-list type)))
    (if (equal result nil)
	(prog2$ (cw "Error(translator): Type ~q0 does not exist!" type)
		nil)
      (cadr result))))

;; ----------------------- translate-number -----------------------------:

;; translate-number
(defun translate-number (num)
  "translate-number: translates ACL2 SMT-number into a Z3 number"
  (if (is-SMT-rational num)
      (list "Q(" (numerator num) "," (denominator num) ")")
    (if (is-SMT-integer num)
	num
      (cw "Error(translator): Cannot translate an unrecognized number: ~q0" num))))

;; ----------------------- translate-variable ---------------------------:

;; translate-variable
(defun translate-variable (var)
  "translate-variable: transalte a SMT variable into Z3 variable"
  (if (is-SMT-variable var)
       var
    (cw "Error(translator): Cannot translate an unrecognized variable: ~q0" var)))

;; ----------------------- translate-constant ---------------------------:

;; translate-const-name 
(defun translate-const-name (const-name)
  "translate-const-name: translate a SMT constant name into Z3"
  (subseq
   (coerce (symbol-name const-name) 'list)
   1 (1- (len const-name))))

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

;; ;; check-const
;; (defun check-const (expr)
;;   "check-const: check to see if an expression is a constant"
;;   (if (and (atom expr)
;; 	   (let ((expr-list (coerce (symbol-name expr) 'list)))
;; 	     (and (equal #\* (car expr-list))
;; 		  (equal #\* (nth (1- (len expr-list)) expr-list)))))
;;       t
;;     nil))

;; ;; get-constant-list-help
;; (defun get-constant-list-help (expr const-list)
;;   "get-constant-list-help: check all constants in a clause"
;;   (cond
;;     ( (consp expr)
;;       (let ((const-list-2 (get-constant-list-help (car expr) const-list)))
;; 	(get-constant-list-help (cdr expr) const-list-2))
;;     )
;;     ( (check-const expr)
;;       (mv-let (keyword name value)
;; 	      (pe expr) ;; pe will not be working for this
;; 	      (cons (list expr (translate-number value)) const-list))
;;       )
;;     ( (atom expr)
;;       (get-constant-list-help (cdr expr) const-list)
;;       )
;;     ( t
;;       const-list
;;       )
;;     )
;;   )

;; ;; get-constant-list
;; (defun get-constant-list (expr)
;;   "get-constant-list: get the list of constants in an associate list"
;;   (get-constant-list-help expr '()))


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
;; make-lambda-list
(defun make-lambda-list (lambda-list)
  "make-lambda-list: translating the binding list of a lambda expression"
  (if (endp (cdr lambda-list))
      (car lambda-list)
    (cons (car lambda-list)
	  (cons '\, (make-lambda-list (cdr lambda-list))))))

;; translate-expression-long
(defun translate-expression-long (expression)
  "translate-expression-long: translate a SMT expression's parameters in ACL2 into Z3 expression"
  (if (endp (cdr expression))
      (translate-expression (car expression))
    (cons (translate-expression (car expression))
	  (cons '\,
		(translate-expression-long
		 (cdr expression))))))

;; stuff.let(['x', 2.0], ['y', v('a')*v('b') + v('c')], ['z', ...]).inn(2*v('x') - v('y'))
;; translate-expression
(defun translate-expression (expression)
  "translate-expression: translate a SMT expression in ACL2 to Z3 expression"
  (if (and (not (equal expression nil))
	   (consp expression)
	   (not (equal expression ''1)))
      (cond ((and (consp (car expression))
		  (is-SMT-operator (caar expression))
		  ;; special treatment for let expression
		  (equal (caar expression) 'lambda))
	     (list '\(
		   (translate-operator (caar expression))
		   #\Space
		   (if (endp (cadr (car expression)))
		       #\Space
		       (make-lambda-list (cadr (car expression))))
		   '\:
		   (translate-expression (caddr (car expression)))
		   '\) '\(
		   (if (endp (cdr expression))
		       #\Space
		       (translate-expression-long (cdr expression)))
		   '\)))
	    ((and (is-SMT-operator (car expression))
		  (equal (car expression) 'list))
	     (list (translate-operator (car expression))
		   '\( '\[
		   (translate-expression-long (cdr expression))
		   '\] '\)))
	    ((is-SMT-operator (car expression))
	     (list (translate-operator (car expression))
		   '\(
		   (translate-expression-long (cdr expression))
		   '\)))
	    (t (list "s.unknown" '\( (translate-expression-long (cdr expression)) '\))))
    (cond ((is-SMT-number expression)
	   (translate-number expression))
	  ((equal expression 'nil) "False") ;; what if when 'nil is a list?
	  ((equal expression 't) "True")
	  ((is-SMT-variable expression)
	   (translate-variable expression))
	  (t (cw "Error(translator): Invalid number or variable: ~q0" expression)))))
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
  (let (;(const-list (car formula))
	(decl-list (cadr formula))
	(hypo-list (caddr formula))
	(concl-list (cadddr formula)))
    (list ;;(translate-constant-list
	  ;;  (get-constant-list formula))
	  (translate-declaration-list decl-list)
	  (translate-hypothesis-list hypo-list)
	  (translate-conclusion-list concl-list)
	  (translate-theorem))))

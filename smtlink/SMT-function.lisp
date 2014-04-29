;; SMT-function
(in-package "ACL2")
(include-book "str/top" :dir :system)

:set-state-ok t
:set-ignore-ok t

;; create-name
(defun create-name (num)
  "create-name: creates a name for a new function"
  (let ((index (str::natstr num)))
    (if (stringp index)
	(mv (intern-in-package-of-symbol
	     (concatenate 'string "var" index) 'ACL2)
	    (1+ num))
      (prog2$ (cw "Error(function): create name failed: ~q0!" index)
	      (mv nil num)))))

;; exist
(defun exist (elem lista)
  "exist: check if an element exist in a list"
  (if (endp lista)
      nil
    (if (equal elem (car lista))
	t
      (exist elem (cdr lista)))))

;; end
(defun end (lista)
  "end: return the last element in a list"
  (if (endp (cdr lista))
      (car lista)
    (end (cdr lista))))

;; replace-var
(defun replace-var (body var-pair)
  "replace-var: replace all appearance of a function symbol in the body with the var-pair"
  (if (atom body)
      (if (equal body (car var-pair))
	  (cadr var-pair)
	body)
    (cons (replace-var (car body) var-pair)
	  (replace-var (cdr body) var-pair))))

;; set-fn-body
(defun set-fn-body (body var-list)
  "set-fn-body: set the body for let expression"
  (if (endp var-list)
      body
    (set-fn-body
     (replace-var body (car var-list))
     (cdr var-list))))

;; make-var-list
(defun make-var-list (formal num)
  "make-var-list: make a list of expressions for replacement"
  (if (endp formal)
      (mv nil num)
    (mv-let (var-name res-num1)
	    (create-name num)
	    (mv-let (res-expr res-num2)
		    (make-var-list (cdr formal) res-num1)
		    (mv (cons (list (car formal) var-name) res-expr) res-num2)))))

;; assoc-fetch-key
(defun assoc-fetch-key (assoc-list)
  "assoc-fetch-key: fetching keys from an associate list"
  (if (endp assoc-list)
      nil
    (cons (caar assoc-list) (assoc-fetch-key (cdr assoc-list)))))

;; assoc-fetch-value
(defun assoc-fetch-value (assoc-list)
  "assoc-fetch-value: fetching values from an associate list"
  (if (endp assoc-list)
      nil
    (cons (cadr (car assoc-list)) (assoc-fetch-value (cdr assoc-list)))))

;; expand-a-fn
;; e.g.(defun double (x y) (+ (* 2 x) y))
;;     (double a b) -> (let ((var1 a) (var2 b)) (+ (* 2 var1) var2))
;;     (double a b) -> ((lambda (var1 var2) (+ (* 2 var1) var2)) a b)
(defun expand-a-fn (fn num state)
  "expand-a-fn: expand an expression with a function definition, num should be accumulated by 1. fn should be stored as a symbol"
  (let ((formal (cdr (cadr (meta-extract-formula fn state))))
	;; the third element is the formals
	(body (end (meta-extract-formula fn state)))
	;; the last element is the body
	)
    (mv-let (var-list num1)
	    (make-var-list formal num)
	    (mv (list 'lambda (assoc-fetch-value var-list)
		      (set-fn-body body var-list))  num1))))

;; lambdap
(defun lambdap (expr)
  "lambdap: check if a formula is a valid lambda expression"
  (if (not (equal (len expr) 3))
      nil
      (let ((lambdax (car expr))
	    (formals (cadr expr))
	    (body (caddr expr)))
	(if (and (equal lambdax 'lambda)
		 (listp formals)) ;; I can add a check for no
	                          ;; occurance of free variable in the future
	    t
	    nil))))

(mutual-recursion
 ;; expand-fn-help-list
 (defun expand-fn-help-list (expr fn-lst num state)
   "expand-fn-help-list"
   (if (endp expr)
       (mv nil num)
     (mv-let (res-expr1 res-num1)
	     (expand-fn-help (car expr) fn-lst num state)
	     (mv-let (res-expr2 res-num2)
		     (expand-fn-help-list (cdr expr) fn-lst res-num1 state)
		     (mv (cons res-expr1 res-expr2) res-num2)))))

 ;; expand-fn-help
 (defun expand-fn-help (expr fn-lst num state)
   "expand-fn-help: expand an expression for one level"
   (cond ((atom expr)
 	  (mv expr num))
 	 ((consp expr) ;; expr is a function application
 	  (b*
 	   ((fn0 (car expr))
 	    (params (cdr expr))
 	    ((mv fn num2)
 	     (cond
 	       ((and (atom fn0) (exist fn0 fn-lst))
 		(expand-a-fn fn0 num state)) ;; expand a function
 	       ((atom fn0)
 		(mv fn0 num))
 	       ((lambdap fn0)
 		(let ((lambdax fn0) (params (cdr expr)))
  		  (let ((formals (cadr lambdax)) (body (caddr lambdax)))
  		    (mv-let (body-expr body-num)
  			    (expand-fn-help body fn-lst num state)
 			    (mv (list 'lambda formals body-expr) body-num)))))
 	       ((and (not (lambdap fn0)) (consp fn0))
 		(expand-fn-help fn0 fn-lst num state))
 	       (t (prog2$ 
 		   (cw "Error(function): not a valid function application ~q0" expr)
 		   (mv expr num))))))
 	   (mv-let (res num3)
 		   (expand-fn-help-list params fn-lst num2 state)
 		   (mv (cons fn res) num3))))
 	 (t (prog2$ (cw "Error(function): strange expression == ~q0" expr)
 		    (mv expr num)))))
)
;; expand-fn
(defun expand-fn (expr fn-lst level num state)
  "expand-fn: takes an expr and a list of functions, unroll the expression to a level using the function definitions. #\Newline
level - level of unrolling; num - starts from 0, for new variables"
  (if (zp level)
      (mv (cons expr nil) num)
    (mv-let (res-expr res-num)
	    (expand-fn-help expr fn-lst num state)
	    (mv-let (res-expr-1 res-num-1)
		    (expand-fn res-expr fn-lst (1- level) res-num state)
		    (mv (cons res-expr res-expr-1) res-num-1)))))

;; expand-fn-top
(defun expand-fn-top (expr fn-lst level state)
  "expand-fn-top: top function for handling expression unrolling."
  (mv-let (res num)
	  (expand-fn expr fn-lst level 0 state)
	  (prog2$ (cw "The final index number: ~q0" num)
		  res)))

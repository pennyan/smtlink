;; SMT-function
(in-package "ACL2")
(include-book "str/top" :dir :system)
(include-book "./helper")

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
(defun expand-a-fn (fn fn-waiting fn-extended num state)
  "expand-a-fn: expand an expression with a function definition, num should be accumulated by 1. fn should be stored as a symbol"
  (let ((formal (cdr (cadr (meta-extract-formula fn state))))
	;; the third element is the formals
	(body (end (meta-extract-formula fn state)))
	;; the last element is the body
	)
    (mv-let (var-list num1)
	    (make-var-list formal num)
	    (mv (list 'lambda (assoc-fetch-value var-list)
		      (set-fn-body body var-list))
		(my-delete fn-waiting fn)
		(cons fn fn-extended)
		num1))))

;; lambdap
(defun lambdap (expr)
  "lambdap: check if a formula is a valid lambda expression"
  (if (not (equal (len expr) 3))
      nil
      (let ((lambdax (car expr))
	    (formals (cadr expr)))
	    ;;(body (caddr expr)))
	(if (and (equal lambdax 'lambda)
		 (listp formals)) ;; I can add a check for no
	                          ;; occurance of free variable in the future
	    t
	    nil))))

(mutual-recursion
 ;; expand-fn-help-list
 (defun expand-fn-help-list (expr fn-lst fn-waiting fn-extended num state)
   "expand-fn-help-list"
   (declare (xargs :measure (list (len fn-waiting) (acl2-count expr))))
   (if (endp expr)
       (mv nil num)
     (mv-let (res-expr1 res-num1)
	     (expand-fn-help (car expr) fn-lst fn-waiting fn-extended num state)
	     (mv-let (res-expr2 res-num2)
		     (expand-fn-help-list (cdr expr) fn-lst fn-waiting fn-extended res-num1 state)
		     (mv (cons res-expr1 res-expr2) res-num2)))))

 ;; expand-fn-help
 ;; This function should keep three lists of function names.
 ;   First one stores all functions possible for expansion.
 ;   Second one is for functions to be expanded
 ;   and the third one is for functions already expanded.
 ;; They should be updated accordingly:
 ;   when one function is expanded along a specific path
 ;   that function should be deleted from fn-waiting and added
 ;   into fn-expanded.
 ;; Resursion detection:
 ;   When one function call is encountered
 ;   we want to make sure that function is valid for expansion
 ;   by looking at fn-lst. Then we expand it, delete it from
 ;   fn-waiting and add it onto fn-expanded. The we want to make
 ;   sure that fn-waiting and fn-expaned is changing as we walk
 ;   through the tree of code.
 ;; Another way of recursion detection:
 ;   One might want to use this simpler way of handling recrusion
 ;   detection. We note the length of fn-lst, then we want to
 ;   count down the level of expansion. Any path exceeding this
 ;   length is a sign for recursive call. 
 (defun expand-fn-help (expr fn-lst fn-waiting fn-extended num state)
   "expand-fn-help: expand an expression"
   (declare (xargs :measure (list (len fn-waiting) (acl2-count expr))))
   (cond ((atom expr) ;; base case, when expr is an atom
 	  (mv expr num))
	 ((consp expr)
	  (let ((fn0 (car expr)) (params (cdr expr)))
	    (cond
	      ((lambdap fn0) ;; function is a lambda expression, expand the body
	       (let ((lambdax fn0) (params (cdr expr)))
		 (let ((formals (cadr lambdax)) (body (caddr lambdax)))
		   (mv-let (res num2)
			   (expand-fn-help body fn-lst fn-waiting fn-extended num state)
			   (mv-let (res2 num3)
				   (expand-fn-help-list params fn-lst fn-waiting fn-extended num2 state)
				   (mv (cons (list 'lambda formals res) res2) num3))))))
	      ((and (not (lambdap fn0)) (consp fn0)) ;; for handling lists 
	       (mv-let (res num2)
		       (expand-fn-help fn0 fn-lst fn-waiting fn-extended num state)
		       (mv-let (res2 num3)
			       (expand-fn-help-list params fn-lst fn-waiting fn-extended num2 state)
			       (mv (cons res res2) num3))))
	      ((and (atom fn0) (exist fn0 fn-lst)) ;; function exists in the list
	       (if (and (exist fn0 fn-waiting) (not (exist fn0 fn-extended))) ;; if fn0 exist in waiting list and not in extended list
		   (mv-let (res fn-w-1 fn-e-1 num2)
			   (expand-a-fn fn0 fn-waiting fn-extended num state) ;; expand a function
			   (mv-let (res2 num3)
				   (expand-fn-help res fn-lst fn-w-1 fn-e-1 num2 state)
				   (mv-let (res3 num4)
					   (expand-fn-help-list params fn-lst fn-waiting fn-extended num3 state)
					   (mv (cons res2 res3) num4))))
		   (prog2$ (cw "Error(function): possible recursive function call detected: ~q0" fn0)
			   (mv expr num))))
	      ((and (consp expr) (atom (car expr))) ;; when expr is a un-expandable function
	       (mv-let (res num2)
		       (expand-fn-help-list (cdr expr) fn-lst fn-waiting fn-extended num state)
		       (mv (cons (car expr) res) num2)))
	      (t (prog2$ 
 		   (cw "Error(function): not a valid function application ~q0" fn0)
 		   (mv expr num)))
	      )))
	 (t (prog2$ (cw "Error(function): strange expression == ~q0" expr)
 		    (mv expr num)))))
)
;; expand-fn
(defun expand-fn (expr fn-lst state)
  "expand-fn: takes an expr and a list of functions, unroll the expression. fn-lst is a list of possible functions for unrolling."
  (mv-let (res-expr res-num)
	  (expand-fn-help expr fn-lst fn-lst nil 0 state)
	  (prog2$ (cw "The final index number: ~q0" res-num) res-expr)))

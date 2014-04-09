;; SMT-function
(in-package "ACL2")
(include-book "str/top" :dir :system)

:set-state-ok t
:set-ignore-ok t

;; pos-int-2-str
;;(defun pos-int-2-str (num)
;;  "pos-int-2-str: translate a positive integer to a string"
;;  (let ((num (nfix num)))
;;  (if (zp (floor num 10))
;;      (list (code-char (+ num 48)))
;;    (concatenate 'LIST
;;		 (pos-int-2-str (floor num 10))
;;		 (list (code-char
;;			(+
;;			 (- num (* 10 (floor num 10)))
;;			 48)))))))

;; integer-to-string
;;(defun integer-to-string (num)
;;  "number-to-string: coerce an integer number into a string"
;;  (cond ((< num 0)
;;	 (concatenate 'STRING "-" (integer-to-string (- 0 num))))
;;	((zp num)
;;	 (string (code-char (+ 0 48))))
;;	(t (coerce (pos-int-2-str num) 'string))))

;; create-name
(defun create-name (num)
  "create-name: creates a name for a new function"
  (let ((index (str::natstr num)))
    (if (stringp index)
	(mv (intern-in-package-of-symbol (concatenate 'string "var" index) 'ACL2) (1+ num))
      (prog2$ (cw "Error: create name failed: ~q0!" index)
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

;; make-var-list
(defun make-var-list (formal num)
  "make-var-list: make the assoc list for formals"
  (if (endp formal)
      (mv nil num)
    (mv-let (var-name res-num1)
	    (create-name num)
	    (mv-let (res-expr res-num2)
		    (make-var-list (cdr formal) res-num1)
		    (mv (cons (list (car formal) var-name) res-expr) res-num2)))))

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

;; make-exp-list
(defun make-exp-list (formal-expr num)
  "make-exp-list: make a list of expressions for replacement"
  (if (endp formal-expr)
      (mv nil num)
    (mv-let (var-name res-num1)
	    (create-name num)
	    (mv-let (res-expr res-num2)
		    (make-exp-list (cdr formal-expr) res-num1)
		    (mv (cons (list var-name (car formal-expr)) res-expr) res-num2)))))

;; expand-a-fn
;; e.g.(defun double (x y) (+ (* 2 x) y))
;;     (double x y) -> (let ((var1 x) (var2 y)) (+ (* 2 var1) var2))
(defun expand-a-fn (expr fn num state)
  "expand-a-fn: expand an expression with a function definition, num should be accumulated by 1. fn should be stored as a symbol"
  (let ((formal (cdr (cadr (meta-extract-formula fn state))))
	;; the third element is the formals
	(body (end (meta-extract-formula fn state)))
	;; the last element is the body
	(formal-expr (cdr expr))
	)
    (mv-let (var-list num1)
	    (make-var-list formal num)
	    (mv-let (expr-list num2)
		    (make-exp-list formal-expr num)
		    (mv (list 'let expr-list (set-fn-body body var-list)) num2)))))

(mutual-recursion
;; expand-fn-help-list
(defun expand-fn-help-list (expr fn-lst num flag state)
  "expand-fn-help-list"
  (if (endp expr)
      (mv nil num)
    (cond ((equal flag 0)
	   (mv-let (res-expr1 res-num1)
		   (expand-fn-help (car expr) fn-lst num state)
		   (mv-let (res-expr2 res-num2)
			   (expand-fn-help-list (cdr expr) fn-lst res-num1 flag state)
			   (mv (cons res-expr1 res-expr2) res-num2))))
	  ((equal flag 1)
	   (mv-let (res-expr1 res-num1)
		   (expand-fn-help (cadr (car expr)) fn-lst num state)
		   (mv-let (res-expr2 res-num2)
			   (expand-fn-help-list (cdr expr) fn-lst res-num1 flag state)
			   (mv (cons (cons (caar expr) (list res-expr1)) res-expr2) res-num2))))
	  (t (prog2$ (cw "Error: no such flag ~q0" flag)
		     (mv nil num))))))

;; expand-fn-help
(defun expand-fn-help (expr fn-lst num state)
  "expand-fn-help: expand an expression for one level"
  (if (atom expr)
      (mv expr num)
    (if (listp expr)
	(cond ((equal (car expr) 'let)
	       (mv-let (res-expr res-num)
		       (expand-fn-help-list (cadr expr) fn-lst num 1 state)
		       (mv (cons (car expr) (cons res-expr (cddr expr))) res-num)))
	      (t (cond ((exist (car expr) fn-lst)
			(expand-a-fn expr (car expr) num state))
		       (t (mv-let (res-expr res-num)
				  (expand-fn-help-list (cdr expr) fn-lst num 0 state)
				  (mv (cons (car expr) res-expr) res-num))))))
      (mv expr num))))
)

;; expand-fn
(defun expand-fn (expr fn-lst level num state)
  "expand-fn: takes an expr and a list of functions, unroll the expression to a level using the function definitions. #\Newline
level - level of unrolling; num - starts from 0, for new variables"
  (if (zp level)
      (mv expr num)
    (mv-let (res-expr res-num)
	    (expand-fn-help expr fn-lst num state)
	    (expand-fn res-expr fn-lst (1- level) res-num state))))

;; expand-fn-top
(defun expand-fn-top (expr fn-lst level state)
  "expand-fn-top: top function for handling expression unrolling."
  (mv-let (res num)
	  (expand-fn expr fn-lst level 0 state)
	  (prog2$ (cw "The final index number: ~q0" num) res)))

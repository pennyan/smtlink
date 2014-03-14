;; Translator takes a set of ACL2 functions,  
;; transform them into a Z3 program and store them 
;; into a .py file. 
;; This is so exciting...

;; The translation I'm going to need:
;; 1. Read from a acl2 file. I need to handle two kinds of basic structure for now.
;;    "defthm" & "defun"
;; 2. Translate corresponding functions and symbols into Z3-python style.
;; 3. Write the results to a corresonding ".py" file.

;; About datatypes. I need to ensure there's no mismatch 
;; on the datatypes. How?

(in-package "ACL2")
(include-book "std/io/top" :dir :system)
;; ---------------------------------- READ OBJECTS INTO A LIST -------------------------------- ;;
;; I don't really need to do the parsing myself. This is really cool. 
;; ACL2 documents support me with this process-file code that helps read the objects of a LISP file
;; into a list. Not sure how this is done, but I think this process is like a parser.
;; Further dig into "read-object" function should give me the explanation to how this is done.
(set-state-ok t)
:logic

;; Read Objects
(defun read-objects-to-list (filename-list state)
  (if (consp filename-list)
    (mv-let (result state) 
            (read-file-objects (car filename-list) state)
            (mv-let (result-list state)
                    (read-objects-to-list (cdr filename-list) state)
                    (mv (cons result result-list) state)))
    (mv nil state)))

;; ------------------------------- TRANSLATE THE PROGRAM LIST -------------------------------- ;;
;; Basically, I recursively walk through the list 
;; and translate the result into another list of Z3 programs.

;; z3-write-constant
(defun head (alist)
  (if (consp alist)
    (if (consp (cdr alist))
      (cons (car alist) (head (cdr alist)))
      nil)
    nil))

(defun simplify-constant (constant-symbol)
  (coerce
   (head
    (cdr
     (coerce (string constant-symbol) 
             'LIST)))
   'STRING))

(defun z3-write-constant (const-declaration)
  (list (simplify-constant (nth 0 const-declaration)) "=" (nth 1 const-declaration) #\Newline))

;; z3-write-function
(defun get-param (alist)
  (if (consp (cdr alist))
    (cons (string (car alist)) (cons "," (get-param (cdr alist))))
    (if (consp alist)
      (list (string (car alist)))
      nil)))

; z3-write-expression
(mutual-recursion
 (defun z3-write-subexpression (alist)
   (if (consp (cdr alist))
       (cond ((consp (car alist))
	      (cons (z3-write-expression (car alist)) 
		    (cons "," (z3-write-subexpression (cdr alist))))) ; if it is a list
	     ((acl2-numberp (car alist))
	      (cons (car alist) 
		    (cons "," (z3-write-subexpression (cdr alist)))))   ; if it is a number
	     ((and (symbolp (car alist)) (equal (car (coerce (string (car alist)) 'LIST)) #\*))
	      (cons (simplify-constant (car alist)) 
		    (cons "," (z3-write-subexpression (cdr alist)))))   
				                      	; special treatment for constant symbols
	     (t (cons (string (car alist)) 
		      (cons "," (z3-write-subexpression (cdr alist)))))) ; else
     (if (consp alist)
         (cond ((consp (car alist))
                (z3-write-expression (car alist))) ; if it is a list
               ((acl2-numberp (car alist))
                (car alist))                       ; if it is a number
               ((and (symbolp (car alist)) (equal (car (coerce (string (car alist)) 'LIST)) #\*))
                (simplify-constant (car alist)))   ; special treatment for constant symbols
               (t (string (car alist))))
         nil)))
 
 (defun z3-write-expression (alist)
   (if (consp alist)
     (cond ((equal (car alist) '+) 
            (list "acl2_plus" "(" (z3-write-subexpression (cdr alist)) ")"))
           ((equal (car alist) '-) 
            (list "acl2_minus" "(" (z3-write-subexpression (cdr alist)) ")"))
           ((equal (car alist) '*) 
            (list "acl2_multiply" "(" (z3-write-subexpression (cdr alist)) ")"))
           ((equal (car alist) '/) 
            (list "acl2_divide" "(" (z3-write-subexpression (cdr alist)) ")"))
           ((equal (car alist) '>) 
            (list "acl2_gt" "(" (z3-write-subexpression (cdr alist)) ")"))
           ((equal (car alist) '<) 
            (list "acl2_st" "(" (z3-write-subexpression (cdr alist)) ")"))
           ((equal (car alist) '>=) 
            (list "acl2_get" "(" (z3-write-subexpression (cdr alist)) ")"))
           ((equal (car alist) '<=) 
            (list "acl2_set" "(" (z3-write-subexpression (cdr alist)) ")"))
           ((equal (car alist) 'equal)
            (list "acl2_equal" "(" (z3-write-subexpression (cdr alist)) ")"))
           ((equal (car alist) 'and)
            (list "acl2_and" "(" (z3-write-subexpression (cdr alist)) ")"))
           ((equal (car alist) 'or)
            (list "acl2_or" "(" (z3-write-subexpression (cdr alist)) ")"))
           ((equal (car alist) 'not)
            (list "acl2_not" "(" (z3-write-subexpression (cdr alist)) ")"))
           ((equal (car alist) 'ACL2-NUMBERP)
            (list "Real" "(" "\""(z3-write-subexpression (cdr alist)) "\"" ")"))
           ((equal (car alist) 'RATIONALP)
            (list "Real" "(" "\"" (z3-write-subexpression (cdr alist)) "\"" ")"))
           ((equal (car alist) 'INTEGERP)
            (list "Int" "(" "\"" (z3-write-subexpression (cdr alist)) "\"" ")"))
           ((equal (car alist) 'COMPLEX-RATIONALP)
            (list "Real" "(" "\"" (z3-write-subexpression (cdr alist)) "\"" ")"))
           (t
            (list (string (car alist)) "(" (z3-write-subexpression (cdr alist)) ")")))
     (if (acl2-numberp alist)
       (list alist)
       (if (symbolp alist)
         alist
         nil))))
 )

(defun z3-write-function (const-declaration)
  (list "def" #\Space (string (nth 0 const-declaration))  
        "(" (get-param (nth 1 const-declaration)) ")" ":"
        "return" #\Space (z3-write-expression (nth 2 const-declaration)) #\Newline))

;; z3-write-theorem
; z3-write-implication

;; We suppose that if there's any declaration about types,
;; they should be within the first AND expression, 
;; others constraints should all be in the second AND expression.
(defun z3-write-type-declaration (declaration-list)
  (if (consp (cdr declaration-list))
    (list (string (car (cdr (car declaration-list)))) "="
	  (z3-write-expression (car declaration-list)) #\Newline 
	  (z3-write-type-declaration (cdr declaration-list)))
    (if (consp declaration-list)
      (list (string (car (cdr (car declaration-list)))) "=" 
	    (z3-write-expression (car declaration-list)))
      nil)))

(defun z3-write-conditions (condition-list)
  (if (or (not (equal (car condition-list) 'and)) (> (len condition-list) 3))
    "Wrong format of condition-list of a theorem!"
    (list (z3-write-type-declaration (cdr (car (cdr condition-list)))) #\Newline 
          (list 
	   "conditions" 
	   "=" 
	   (z3-write-expression (car (cdr (cdr condition-list)))) #\Newline))))

(defun z3-write-conclusion (conclusion-list)
  (z3-write-expression conclusion-list))

(defun z3-write-implication (alist)
  (if (equal (car alist) 'IMPLIES)
    (list (list (z3-write-conditions (car (cdr alist))))
          (list "conclusion" "=" 
		(z3-write-conclusion (car (cdr (cdr alist)))) #\Newline))
    (list (list "conditions" "=" "True" #\Newline) 
          (list "conclusion" "=" (z3-write-conclusion alist) #\Newline))))

(defun z3-write-theorem (const-declaration)
  (cons (z3-write-implication (car (cdr const-declaration)))
        (list "prove" 
              "(" "Implies" "(" "conditions" "," "conclusion" ")" ")" #\Newline)))

;; translating a line of code
(defun translate-code (code)
  (if (consp code)
    (let ((x (car code)))
      (cond ((equal x 'DEFCONST) (z3-write-constant (cdr code)))
            ((equal x 'DEFUN) (z3-write-function (cdr code)))
            ((equal x 'DEFTHM) (z3-write-theorem (cdr code)))))
    nil))

;; translating a file
(defun translate-file (list-of-code)
  (if (consp list-of-code)
    (cons (translate-code (car list-of-code)) (translate-file (cdr list-of-code)))
    nil))

;; translating a list of files
(defun translator (list-of-files)
  (if (consp list-of-files)          
    (cons (translate-file (car list-of-files)) (translator (cdr list-of-files)))
    nil))

;; ----------------------------- TEST FUNCTION ----------------------------- ;;
;; test case: (translate-from-ACL2-to-Z3-test '("testglobal.lisp" "testfunction.lisp" "testthm.lisp") state)
(defun translate-from-ACL2-to-Z3-test (file-list state)
  (mv-let (ACL2-code state)
          (read-objects-to-list file-list state)
          (let ((Z3-code (translator ACL2-code)))     ; write-out function undefined
            (mv Z3-code state))))

;; ---------------------------------- WRITE LIST TO FILE ------------------------------------ ;;
;; Problems:
;; 1. Careful for python indentation
;; 2. When to change to next line

(defun princ$-list-of-strings (alist channel state)
  (if (consp alist)
    (let ((state (princ$-list-of-strings (car alist) channel state)))
      (princ$-list-of-strings (cdr alist) channel state))
    (if (and (not (equal alist nil)) 
	     (not (acl2-numberp alist)))   ;; if alist is a number, should be treated seperately
      (princ$ (string alist) channel state)
      (if (acl2-numberp alist)
        (princ$ alist channel state)
        state))))

(defun write-list-to-file (filename alist state)
  (mv-let
   (channel state)
   (open-output-channel filename :character state)
   (let ((state (princ$-list-of-strings 
		 (coerce (append (coerce "from ACL2\_translator import *" 'LIST) 
				 (list #\Newline)) 
			 'STRING) 
		 channel state)))
     (let ((state (princ$-list-of-strings alist channel state)))
       (close-output-channel channel state)))))

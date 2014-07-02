(in-package "ACL2")
(include-book "./SMT-translator")
(include-book "./SMT-run")
(include-book "./SMT-interpreter")
(include-book "./SMT-function")
(include-book "./helper")

(mutual-recursion
;; lisp-code-print-help
(defun lisp-code-print-help (lisp-code-list indent)
  "lisp-code-print-help: make a printable lisp code list"
  (if (endp lisp-code-list)
      nil
    (list #\Space
	  (lisp-code-print (car lisp-code-list) indent)
	  (lisp-code-print-help (cdr lisp-code-list) indent))))
 
;; lisp-code-print: make printable lisp list
(defun lisp-code-print (lisp-code indent)
  "lisp-code-print: make a printable lisp code list"
  (cond ((equal lisp-code 'nil) "nil") ;; 
	((equal lisp-code 'quote) "'") ;; quote
	((atom lisp-code) lisp-code)
	((and (equal 2 (length lisp-code))
	      (equal (car lisp-code) 'quote))
	 (cons "'"
	       (lisp-code-print (cadr lisp-code)
				(cons #\Space
				      (cons #\Space indent)))))
	(t
	 (list #\Newline indent '\(
	       (cons (lisp-code-print (car lisp-code)
				      (cons #\Space
					    (cons #\Space indent)))
		     (lisp-code-print-help (cdr lisp-code)
					   (cons #\Space
						 (cons #\Space indent))))
	       '\) ))))
)

;; my-prove-SMT-formula
(defun my-prove-SMT-formula (term)
  "my-prove-SMT-formula: check if term is a valid SMT formula"
  (let ((decl-list (cadr (cadr term)))
	(hypo-list (caddr (cadr term)))
	(concl-list (caddr term)))
    (SMT-formula '()
		 decl-list
		 hypo-list
		 concl-list)))

;; my-prove-write-file
(defun my-prove-write-file (term fdir)
  "my-prove-write-file: write translated term into a file"
  (write-SMT-file fdir
		  (translate-SMT-formula
		   (my-prove-SMT-formula term))
		  state))

;; my-prove-write-expander-file
(defun my-prove-write-expander-file (expanded-term fdir)
  "my-prove-write-expander-file: write expanded term into a log file"
  (write-expander-file fdir
		       expanded-term
		       state))

;; create-level
(defun create-level (level index)
  "create-level: creates a name for a level"
  (intern-in-package-of-symbol
   (concatenate 'string level (str::natstr index)) 'ACL2))

;; my-prove-build-log-file
(defun my-prove-build-log-file (expanded-term-list index)
  "my-prove-build-log-file: write the log file for expanding the functions"
  (if (endp expanded-term-list)
      nil
      (cons (list (create-level "level " index) '\:
		  (lisp-code-print
		   (car expanded-term-list) '())
		  #\Newline #\Newline)
	    (my-prove-build-log-file
	     (cdr expanded-term-list) (1+ index)))))

;; translate added hypothesis to underling representation
(defun translate-hypo (hypo)
  "translate-hypo: translate added hypothesis to underling representation"
  (if (endp hypo)
      nil
      (cons (mv-let (erp res state)
		    (translate (car hypo) t nil t nil (w state) state)
		    (if (endp res) (car hypo) res))
	    (translate-hypo (cdr hypo)))))

;; translate a let binding for added hypothesis
(defun translate-let (let-expr)
  "translate-let: translate a let binding for added hypo"
  (if (endp let-expr)
      nil
      (cons (list (caar let-expr)
		  (mv-let (erp res state)
			  (translate (cadar let-expr) t nil t nil (w state) state)
			  (if (endp res) (cadar let-expr) res))
		  (caddar let-expr))
	    (translate-let (cdr let-expr)))))

;; get-hint-formula
(defun get-hint-formula (name)
  "get-hint-formula: get the formula by a hint's name"
  (formula name t (w state)))

;; add-hints
(defun add-hints (hints clause)
  "add-hints: add a list of hint to a clause, in the form of ((not hint3) ((not hint2) ((not hint1) clause)))"
  (if (endp hints)
      clause
      (add-hints (cdr hints)
		 (cons (list 'not (get-hint-formula (car hints))) clause))))

;; construct augmented result
(defun augment-hypothesis (rewritten-term let-expr orig-param main-hints)
  "augment-hypothesis: augment the returned clause with \
new hypothesis in lambda expression"
  (if (endp main-hints)
      (list (list 'not
      (cons (list 'lambda (append (assoc-get-key let-expr) orig-param) rewritten-term)
	    (append (assoc-get-value let-expr) orig-param))))
      (if (endp let-expr)
	  rewritten-term
	  (add-hints main-hints
		     (list (list 'not
		      (cons (list 'lambda (append (assoc-get-key let-expr) orig-param) rewritten-term)
			    (append (assoc-get-value let-expr) orig-param))))))))

;;separate-type
(defun separate-type (let-expr)
  "separate-type: separate let expression types from let expression, I do it in this way for convenience. I might want to use them as a whole in the future."
  (if (endp let-expr)
      (mv nil nil)
      (mv-let (res-let-expr res-let-type)
	      (separate-type (cdr let-expr))
	      (mv (cons (list (caar let-expr) (cadar let-expr))
			res-let-expr)
		  (cons (caddar let-expr)
			res-let-type)))))

;; create-type-theorem
(defun create-type-theorem (decl-hypo-list let-expr let-type let-hints)
  "create-type-theorem"
  (if (endp let-hints)
      (create-type-theorem-helper-no-hints decl-hypo-list let-expr let-type)
      (create-type-theorem-helper-with-hints decl-hypo-list let-expr let-type let-hints)))

(defun create-type-theorem-helper-no-hints (decl-hypo-list let-expr let-type)
  (if (endp let-expr)
      nil
      (cons (list (list 'not
			(list 'if (cadr decl-hypo-list)
			      (append-and-hypo (caddr decl-hypo-list)
					       (list (list 'equal (caar let-expr) (cadar let-expr))))
			      ''nil))
		  (list (car let-type) (caar let-expr)))
	    (create-type-theorem-helper-no-hints decl-hypo-list (cdr let-expr) (cdr let-type)))))

(defun create-type-theorem-helper-with-hints (decl-hypo-list let-expr let-type let-hints)
  (if (endp let-expr)
      nil
      (cons (add-hints (car let-hints)
		       (list (list 'not
				   (list 'if (cadr decl-hypo-list)
					 (append-and-hypo (caddr decl-hypo-list)
							  (list (list 'equal (caar let-expr) (cadar let-expr))))
					 ''nil))
			     (list (car let-type) (caar let-expr))))
	    (create-type-theorem-helper-with-hints decl-hypo-list (cdr let-expr) (cdr let-type) (cdr let-hints)))))

;; create-hypo-theorem
(defun create-hypo-theorem (decl-hypo-list let-expr hypo-expr orig-param hypo-hints)
  "create-hypo-theorem: create a theorem for proving user added hypothesis"
  (if (endp hypo-hints)
      (create-hypo-theorem-helper-no-hints decl-hypo-list let-expr hypo-expr orig-param)
      (create-hypo-theorem-helper-with-hints decl-hypo-list let-expr hypo-expr orig-param hypo-hints)))

(defun create-hypo-theorem-helper-no-hints (decl-hypo-list let-expr hypo-expr orig-param)
  (if (endp hypo-expr)
      nil
      (cons (list (list 'not decl-hypo-list)
		  (cons (list 'lambda (append (assoc-get-key let-expr) orig-param) (car hypo-expr))
			(append (assoc-get-value let-expr) orig-param)))
	    (create-hypo-theorem-helper-no-hints decl-hypo-list let-expr (cdr hypo-expr) orig-param))))

(defun create-hypo-theorem-helper-with-hints (decl-hypo-list let-expr hypo-expr orig-param hypo-hints)
  (if (endp hypo-expr)
      nil
      (cons (add-hints (car hypo-hints)
	     (list (list 'not decl-hypo-list)
		   (cons (list 'lambda (append (assoc-get-key let-expr) orig-param) (car hypo-expr))
			 (append (assoc-get-value let-expr) orig-param))))
	    (create-hypo-theorem-helper-with-hints decl-hypo-list let-expr (cdr hypo-expr) orig-param (cdr hypo-hints)))))

;; my-prove
(defun my-prove (term fn-lst fn-level fname let-expr new-hypo let-hints hypo-hints main-hints)
  "my-prove: return the result of calling SMT procedure"
  (let ((file-dir (concatenate 'string
			       *dir-files*
			       "/"
			       fname
			       ".py"))
	(expand-dir (concatenate 'string
				 *dir-expanded*
				 "/"
				 fname
				 "\_expand.log")))
    (let ((let-expr-translated-with-type (translate-let let-expr))
	  (hypo-translated (translate-hypo new-hypo)))
      (mv-let (let-expr-translated let-type)
	      (separate-type let-expr-translated-with-type)
	      (mv-let (expanded-term-list num orig-param)
		      (expand-fn term fn-lst fn-level let-expr-translated let-type hypo-translated state)
		      (prog2$ (cw "Expanded(SMT-z3): ~q0 Final index number: ~q1" expanded-term-list num)
			      (prog2$ (my-prove-write-expander-file
				       (my-prove-build-log-file
					(cons term expanded-term-list) 0)
				       expand-dir)
				      (prog2$ (my-prove-write-file
					       expanded-term-list
					       file-dir)
					      (let ((type-theorem (create-type-theorem (cadr term)
										       let-expr-translated
										       let-type
						                                       let-hints))
						    (hypo-theorem (create-hypo-theorem (cadr term)
										       let-expr-translated
										       hypo-translated
										       orig-param
										       hypo-hints))
						    (aug-theorem (augment-hypothesis (caddr expanded-term-list)
										     let-expr-translated
										     orig-param
										     main-hints)))
						(if (car (SMT-interpreter file-dir))
						    (mv t aug-theorem type-theorem hypo-theorem)
						    (mv nil aug-theorem type-theorem hypo-theorem)))))))))))

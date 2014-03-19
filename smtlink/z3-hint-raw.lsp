(include-book "./SMT-formula")
(include-book "./translate-SMT-formula")
(include-book "./SMT-run")
(include-book "./SMT-interpreter")

(tshell-ensure)

(defun my-prove-SMT-formula (term)
  (let ((decl-list (cadr (cadr term)))
	(hypo-list (caddr (cadr term)))
	(concl-list (caddr term)))
    (prog2$ (cw "~q0" decl-list)
    (SMT-formula '((const1 1))
		 decl-list
		 hypo-list
		 concl-list))))

(defun my-prove-write-file (term)
  (write-SMT-file "z3_files/test.py"
		  (translate-SMT-formula
		   (my-prove-SMT-formula term))
		  state))

(defun my-prove (term)
  (prog2$ (my-prove-write-file term)
	  (if (car (SMT-interpreter "python" "z3_files/test.py"))
	      t
	    nil)))

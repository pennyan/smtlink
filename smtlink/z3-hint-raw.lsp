(include-book "./SMT-formula")
(include-book "./translate-SMT-formula")
(include-book "./SMT-run")
(include-book "./SMT-interpreter")

(defun declaration-format (decl)
  (cdr decl))

(defun hypothesis-format (hypo)
  hypo)

(defun conclusion-format (concl)
  concl)

(tshell-ensure)

(defun my-prove-SMT-formula (term)
  (let ((decl-list (declaration-format (cadr (cadr term))))
	(hypo-list (hypothesis-format (caddr (cadr term))))
	(concl-list (conclusion-format (caddr term))))
    (prog2$ (cw "~q0, ~q1, ~q2" decl-list hypo-list concl-list)
	    (SMT-formula-top :const-list ()
			     :decl-list decl-list
			     :hyp-list hypo-list
			     :concl-list concl-list))))

(defun my-prove-SMT-translate (term)
  (translate-SMT-formula
   (prog2$ (cw "~q0" (my-prove-SMT-formula term))
	   (my-prove-SMT-formula term))))

(defun my-prove-write-file (term)
  (write-SMT-file "z3_files/test.py"
		  (translate-SMT-formula
		   (my-prove-SMT-formula term))
		  state))

(defun my-prove (term hint)
  (prog2$ (my-prove-write-file term)
	  (if (equal (car (SMT-interpreter "python" "z3_files/test.py")) t)
	      t
	    nil)))

(include-book "./SMT-formula")
(include-book "./SMT-translator")
(include-book "./SMT-run")
(include-book "./SMT-interpreter")

(tshell-ensure)

(defun my-prove-SMT-formula (term)
  (let ((decl-list (cadr (cadr term)))
	(hypo-list (caddr (cadr term)))
	(concl-list (caddr term)))
    (SMT-formula '((const1 1))
		 decl-list
		 hypo-list
		 concl-list)))

(defun my-prove-write-file (term fdir)
  (write-SMT-file fdir
		  (translate-SMT-formula
		   (my-prove-SMT-formula term))
		  state))

(defun my-prove (term fname)
  (let ((file-dir (concatenate 'string
			       *dir-files*
			       "/"
			       fname
			       ".py")))
    (prog2$ (my-prove-write-file term file-dir)
	    (if (car (SMT-interpreter file-dir))
		t
	      nil))))

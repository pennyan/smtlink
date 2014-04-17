(include-book "./SMT-formula")
(include-book "./SMT-translator")
(include-book "./SMT-run")
(include-book "./SMT-interpreter")
(include-book "./SMT-function")

(tshell-ensure)

(defun my-prove-SMT-formula (term)
  (let ((decl-list (cadr (cadr term)))
	(hypo-list (caddr (cadr term)))
	(concl-list (caddr term)))
    (SMT-formula '()
		 decl-list
		 hypo-list
		 concl-list)))

(defun my-prove-write-file (term fdir)
  (write-SMT-file fdir
		  (translate-SMT-formula
		   (my-prove-SMT-formula term))
		  state))

(defun my-prove (term fn-lst level fname)
  (let ((file-dir (concatenate 'string
			       *dir-files*
			       "/"
			       fname
			       ".py")))
    (mv-let (expanded-term num)
	    (expand-fn-top term fn-lst level state)
	    (prog2$ (cw "~q0 ~%" expanded-term)
	    (prog2$ (my-prove-write-file expanded-term file-dir)
		    (if (car (SMT-interpreter file-dir))
			(mv t expanded-term)
		      (mv nil expanded-term)))))))

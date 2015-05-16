;;SMT-interpreter formats the results

(in-package "ACL2")
(include-book "SMT-run")
(include-book "config")
(defttag :tshell)

;; SMT-interpreter
(defun SMT-interpreter (filename smt-cnf)
  "SMT-intepreter: get the result returned from calling SMT procedure"
  (mv-let (finishedp exit-status lines)
          (SMT-run filename smt-cnf)
	  (cond ((equal finishedp nil) 
		 (cw "Warning: the command was interrupted."))
		((not (equal exit-status 0)) 
		 (cw "Z3 failure: ~q0" lines))
		(t (if (equal (car lines) "proved")
		       t
		     (cw "~q0" lines))))))

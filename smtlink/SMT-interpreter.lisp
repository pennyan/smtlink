;;SMT-interpreter formats the results

(in-package "ACL2")

;; SMT-interpreter
(defun SMT-interpreter (z3-cmd filename)
  "SMT-intepreter: get the result returned from calling SMT procedure"
  (mv-let (finishedp exit-status lines)
          (SMT-run z3-cmd filename)
	  (cond ((equal finishedp nil) 
		 (cw "Warning: the command was interrupted."))
		((not (equal exit-status 0)) 
		 (cw "Z3 failure: ~q0" lines))
		(t (if (equal (car lines) "proved")
		       t
		     (cw "~q0" lines))))))

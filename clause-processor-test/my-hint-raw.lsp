(defun my-prove (term)
  (prog2$ (cw "first is equal ~q0" term)
	  (if (equal (car term) 'equal)
	      (prog2$ (cw "second if ~q0 =?= ~q1" (cadr term) (caddr term))
		      (if (equal (+ (eval (cadr term)) 1) (eval (caddr term)))
			  t
			nil))
	    nil)))

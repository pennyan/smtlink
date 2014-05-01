(in-package "ACL2")

(defstub acl2-my-prove (term fn-lst level fname) (mv t nil))

(program)

(defttag :my-cl-proc)

(set-ignore-ok t)

(progn

; We wrap everything here in a single progn, so that the entire form is
; atomic.  That's important because we want the use of push-untouchable to
; prevent anything besides my-clause-processor from calling acl2-my-prove.

  (progn!

   (set-raw-mode-on state)

   (load "../smtlink/z3-hint-raw.lsp") ; defines my-prove in raw Lisp
   
   (defun acl2-my-prove (term fn-lst level fname)
     (my-prove term fn-lst level fname)))

  ;; put fn-lst level and fname into the hint list
  (defun my-clause-processor (cl hint)
    (declare (xargs :guard (pseudo-term-listp cl)
                    :mode :program))
    (prog2$ (cw "Original clause(connect): ~q0" (disjoin cl))
    (let ((fn-lst (car hint))
	  (level (cadr hint))
	  (fname (caddr hint)))
      (mv-let (res expanded-cl)
	      (acl2-my-prove (disjoin cl) fn-lst level fname)
	      (if res
		  (prog2$ (cw "Expanded clause(connect): ~q0 ~% Success!~%" expanded-cl)
			  (list (cons (list 'not expanded-cl) cl)))
		(prog2$ (cw "~|~%NOTE: Unable to prove goal with ~
                  my-clause-processor and indicated hint.~|")
			(list cl)))))))

  (push-untouchable acl2-my-prove t)
  )

(define-trusted-clause-processor
  my-clause-processor
  nil
  :ttag my-cl-proc)

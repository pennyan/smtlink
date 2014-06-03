(in-package "ACL2")

(defstub acl2-my-prove (term fn-lst fname let-expr new-hypo) (mv t nil nil))

(program)

(defttag :my-cl-proc)

(progn

; We wrap everything here in a single progn, so that the entire form is
; atomic.  That's important because we want the use of push-untouchable to
; prevent anything besides my-clause-processor from calling acl2-my-prove.

  (progn!

   (set-raw-mode-on state) ;; conflict with assoc, should use assoc-equal, not assoc-eq

   (load "../smtlink/SMT-z3.lisp")

   (defun acl2-my-prove (term fn-lst fname let-expr new-hypo)
     (my-prove term fn-lst fname let-expr new-hypo)))
  
  ;; put fn-lst level and fname into the hint list
  (defun my-clause-processor (cl hint)
    (declare (xargs :guard (pseudo-term-listp cl)
                    :mode :program))
    (prog2$ (cw "Original clause(connect): ~q0"
	        (disjoin cl))
    (let ((fn-lst (cadr (assoc ':expand hint)))
	  (fname (cadr (assoc ':python-file hint)))
	  (let-expr (cadr (assoc ':let hint)))
	  ;; translate formulas in let associate list into underling representation
	  (new-hypo (cadr (assoc ':hypothesize hint))))
      (mv-let (res expanded-cl type-related-theorem)
	      (acl2-my-prove (disjoin cl) fn-lst fname let-expr new-hypo)
	      (if res
		  (if (not (equal type-related-theorem nil))
		      (let ((res-clause (cons (cons (list 'not expanded-cl) cl) type-related-theorem)))
			(prog2$ (cw "Expanded clause(connect): ~q0 ~% Success!~%" res-clause) res-clause))
		      (let ((res-clause (list (cons (list 'not expanded-cl) cl))))
			(prog2$ (cw "Expanded clause(connect): ~q0 ~% Success!~%" res-clause) res-clause)))
		  (prog2$ (cw "~|~%NOTE: Unable to prove goal with ~
                                 my-clause-processor and indicated hint.~|")
			  (list cl)))))))

  (push-untouchable acl2-my-prove t)
  )

(define-trusted-clause-processor
  my-clause-processor
  nil
  :ttag my-cl-proc)


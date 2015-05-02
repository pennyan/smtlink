;;
;; This file is adapted from :doc define-trusted-clause-processor
;; The dependent files, instead of being in raw Lisp, are in ACL2.
;; That makes me doubt if I really need to do defstub, progn,
;; progn!, and push-untouchable...
;;
;; However, I'm using them right now in case if there are
;; behaviours with those constructs that are not known to me.
;;
(in-package "ACL2")
(include-book "tools/bstar" :dir :system)
(set-state-ok t)

(defstub acl2-my-prove
  (term fn-lst fn-level fname let-expr new-hypo let-hints hypo-hints main-hints state)
  (mv t nil nil nil nil state))

(program)
(defttag :Smtlink)

(include-book "SMT-z3")
(value-triple (tshell-ensure))

(progn

; We wrap everything here in a single progn, so that the entire form is
; atomic.  That's important because we want the use of push-untouchable to
; prevent anything besides my-clause-processor from calling acl2-my-prove.

  (progn!

   (set-raw-mode-on state) ;; conflict with assoc, should use assoc-equal, not assoc-eq
   
   (defun acl2-my-prove (term fn-lst fn-level fname let-expr new-hypo let-hints hypo-hints main-hints state)
     (my-prove term fn-lst fn-level fname let-expr new-hypo let-hints hypo-hints main-hints state))
   )

  (defun Smtlink-arguments (hint)
    (b* ((fn-lst (cadr (assoc ':functions
			      (cadr (assoc ':expand hint)))))
	 (fn-level (cadr (assoc ':expansion-level
				(cadr (assoc ':expand hint)))))
	 (fname (cadr (assoc ':python-file hint)))
	 (let-expr (cadr (assoc ':let hint)))
	 (new-hypo (cadr (assoc ':hypothesize hint)))
	 (let-hints (cadr (assoc ':type
				 (cadr (assoc ':use hint)))))
	 (hypo-hints (cadr (assoc ':hypo
				  (cadr (assoc ':use hint)))))
	 (main-hints (cadr (assoc ':main
				  (cadr (assoc ':use hint))))))
	(mv fn-lst fn-level fname let-expr new-hypo let-hints hypo-hints main-hints))
    )
  
  (defun Smtlink (cl hint state)
    (declare (xargs :guard (pseudo-term-listp cl)
                    :mode :program))
    (prog2$ (cw "Original clause(connect): ~q0" (disjoin cl))
    (b* (((mv fn-lst fn-level fname let-expr new-hypo let-hints hypo-hints main-hints)
	  (Smtlink-arguments hint)))
      (mv-let (res expanded-cl type-related-theorem hypo-theorem fn-type-theorem state)
	      (acl2-my-prove (disjoin cl) fn-lst fn-level fname let-expr new-hypo let-hints hypo-hints main-hints state)
	      (if res
		  (let ((res-clause (append (append (append fn-type-theorem type-related-theorem) hypo-theorem)
					    (list (append expanded-cl cl))
					    )))
		    (prog2$ (cw "Expanded clause(connect): ~q0 ~% Success!~%" res-clause)
			    (mv nil res-clause state)))
		  (prog2$ (cw "~|~%NOTE: Unable to prove goal with ~
                                 my-clause-processor and indicated hint.~|")
			  (mv t (list cl) state)))))))
  
  (push-untouchable acl2-my-prove t)
  )

(define-trusted-clause-processor
  Smtlink
  nil
  :ttag Smtlink)

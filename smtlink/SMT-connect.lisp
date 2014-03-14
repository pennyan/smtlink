(defstub acl2-my-prove (term hint) t)

(program)

(defttag :my-cl-proc)

(progn

; We wrap everything here in a single progn, so that the entire form is
; atomic.  That's important because we want the use of push-untouchable to
; prevent anything besides my-clause-processor from calling acl2-my-prove.

  (progn!

   (set-raw-mode-on state)

   (load "z3-hint-raw.lsp") ; defines my-prove in raw Lisp

   (defun acl2-my-prove (term hint)
     (my-prove term hint)))

  (defun my-clause-processor (cl hint)
    (declare (xargs :guard (pseudo-term-listp cl)
                    :mode :program))
    (if (acl2-my-prove (disjoin cl) hint)
      (list (list hint))
      (prog2$ (cw "~|~%NOTE: Unable to prove goal with ~
                  my-clause-processor and indicated hint.~|")
              (list cl))))

  (push-untouchable acl2-my-prove t)
  )

(define-trusted-clause-processor
  my-clause-processor
  nil
  :ttag my-cl-proc)

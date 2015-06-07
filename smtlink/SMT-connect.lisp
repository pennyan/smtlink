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
(set-ignore-ok t)

(defstub acl2-my-prove
  (term fn-lst fn-level uninterpreted fname let-expr new-hypo let-hints hypo-hints main-hints smt-config state)
  (mv t nil nil nil nil state))

(program)
(defttag :Smtlink)

(include-book "SMT-py")
(include-book "config")
(value-triple (tshell-ensure))

(progn
; We wrap everything here in a single progn, so that the entire form is
; atomic.  That's important because we want the use of push-untouchable to
; prevent anything besides Smtlink-raw from calling acl2-my-prove.

  (progn!

   (set-raw-mode-on state) ;; conflict with assoc, should use assoc-equal, not assoc-eq
   
   (defun acl2-my-prove (term fn-lst fn-level uninterpreted fname let-expr new-hypo let-hints hypo-hints main-hints smt-config state)
     (my-prove term fn-lst fn-level uninterpreted fname let-expr new-hypo let-hints hypo-hints main-hints smt-config state))
   )

  ;; Supported arguments:
  ;; expand - functions : a list of functions to be expanded
  ;;          expansion-level : how many levels to expand a function
  ;; uninterpreted-functions : a list of functions taken as uninterpreted functions after the expansion
  ;; python-file : specify the file name of the python file to write to
  ;; let : specify to replace a sub-expression as a variable
  ;; hypothesis : specify hypotheses about those variables introduces by let-expr
  ;; use - type : hints for type predicates from function expansion
  ;;       hypo : hints for sub-expression hypotheses
  ;;       main : hints for the main clause returned
  (defun Smtlink-arguments (hint)
    (b* ((fn-lst (cadr (assoc ':functions
                              (cadr (assoc ':expand hint)))))
         (fn-level (cadr (assoc ':expansion-level
                                (cadr (assoc ':expand hint)))))
         (uninterpreted (cadr (assoc ':uninterpreted-functions hint)))
         (fname (cadr (assoc ':python-file hint)))
         (let-expr (cadr (assoc ':let hint)))
         (new-hypo (cadr (assoc ':hypothesize hint)))
         (let-hints (cadr (assoc ':let
                                 (cadr (assoc ':use hint)))))
         (hypo-hints (cadr (assoc ':hypo
                                  (cadr (assoc ':use hint)))))
         (main-hints (cadr (assoc ':main
                                  (cadr (assoc ':use hint))))))
        ;; do sanity check
        ;; (cond ((and (endp fn-lst) (not (endp uninterpreted)))
        ;;        (prog2$ (cw "Error(connect): only uninterpreted function is provided. No return type provided.~%")
        ;;                (mv nil nil nil nil nil nil nil nil nil)))
        ;;       (t (mv fn-lst fn-level uninterpreted fname let-expr new-hypo let-hints hypo-hints main-hints)))
        (mv fn-lst fn-level uninterpreted fname let-expr new-hypo let-hints hypo-hints main-hints)
        )
    )
  
  (defun Smtlink-raw (cl hint state custom-config)
    (declare (xargs :guard (pseudo-term-listp cl)
                    :mode :program))
    (prog2$ (cw "Original clause(connect): ~x0" cl)
    (b* (((mv fn-lst fn-level uninterpreted fname let-expr new-hypo let-hints hypo-hints main-hints)
	  (Smtlink-arguments hint)))
      (mv-let (res expanded-cl type-related-theorem hypo-theorem fn-type-theorem state)
	      (acl2-my-prove (disjoin cl) fn-lst fn-level uninterpreted fname let-expr new-hypo let-hints hypo-hints main-hints (if custom-config (smt-cnf) (default-smtlink-config)) state)
	      (if res
		  (let ((res-clause (append (append (append fn-type-theorem type-related-theorem) hypo-theorem)
					    (list (append expanded-cl cl))
					    )))
		    (prog2$ (cw "Expanded clause(connect): ~q0 ~% Success!~%" "hello-world") ; res-clause)
			    (mv nil res-clause state)))
		  (prog2$ (cw "~|~%NOTE: Unable to prove goal with ~
                                 my-clause-processor and indicated hint.~|")
			  (mv t (list cl) state)))))))

  (defun Smtlink (cl hint state)
    (declare (xargs :guard (pseudo-term-listp cl)
                    :mode :program))
    (if (equal (smt-cnf) (default-smtlink-config))
        (Smtlink-raw cl hint state nil)
      (mv (er hard? 'top-level "Error(connect): You've defined a user configuration, are you sure you want to use Smtlink, instead of Smtlink-custom-config?")
          (list cl)
          state)))

  (defun Smtlink-custom-config (cl hint state)
    (declare (xargs :guard (pseudo-term-listp cl)
                    :mode :program))
    (if (not (equal (smt-cnf) (default-smtlink-config)))
        (Smtlink-raw cl hint state t)
      (mv (er hard? 'top-level "Error(connect): You haven't defined any customed configuration yet, or you haven't changed anything in the configuration. Please use Smtlink instead of Smtlink-custom-config.")
          (list cl)
          state)))

  (push-untouchable acl2-my-prove t)
  )

(define-trusted-clause-processor
  Smtlink
  nil
  :ttag Smtlink)

(define-trusted-clause-processor
  Smtlink-custom-config
  nil
  :ttag Smtlink-custom-config)


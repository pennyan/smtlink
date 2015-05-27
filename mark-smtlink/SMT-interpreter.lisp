;;SMT-interpreter formats the results

(in-package "ACL2")
(include-book "SMT-run")
(include-book "config")
(defttag :tshell)

;; ;; parse-counter-example
;; (defun parse-counter-example (ce-str)
;;   "parse-counter-example: parse a counter example string returned by Z3"
;;   ())

;; ;; fire-session
;; (defun fire-session (lines)
;;   ()
;;   )

;; SMT-interpreter
;; If failed, one needs to fire off a raw lisp session
;; and bind all variables with values.
;; Need to tell user informations on how to leave the
;; session.
(defun SMT-interpreter (filename smt-config)
  "SMT-intepreter: get the result returned from calling SMT procedure"
  (mv-let (finishedp exit-status lines)
          (SMT-run filename smt-config)
	  (cond ((equal finishedp nil)
		 (cw "Warning: the command was interrupted."))
		((not (equal exit-status 0))
		 (cw "Z3 failure: ~q0" lines))
		(t (if (equal (car lines) "proved")
		       t
         ;;(fire-session lines)
         (cw "~q0" lines)
         ))))
  )

;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software
;;

(in-package "SMT")
(include-book "tools/bstar" :dir :system)
(include-book "SMT-prove")
(set-state-ok t)

(defsection SMT-trusted-cp
  :parent (Smtlink)
  :short "The trusted clause processor"


(defstub SMT-prove-stub (term smtlink-hint state) (mv t state))

(program)
(defttag :Smtlink)

(progn

; We wrap everything here in a single progn, so that the entire form is
; atomic.  That's important because we want the use of push-untouchable to
; prevent anything besides SMT-proves-stub from calling SMT-prove.

  (progn!

   (set-raw-mode-on state)

   (defun SMT-prove-stub (term smtlink-hint state)
     (SMT-prove term smtlink-hint state)))

  (defun SMT-trusted-cp (cl smtlink-hint state)
    (declare (xargs :stobjs state
                    :guard (pseudo-term-listp cl)
                    :mode :program))
    (b* ((- (cw "clause given to the trusted clause processor: ~q0"  cl))
         (- (cw ""))
         ((mv res state) (SMT-prove-stub (disjoin cl) smtlink-hint state)))
      (if res
          (prog2$ (cw "Proved!~%") (mv nil nil state))
        (prog2$ (cw "~|~%NOTE: Unable to prove goal with ~
                      SMT-trusted-cp and indicated hint.~|")
                (mv t (list cl) state)))))

  (push-untouchable SMT-prove-stub t)
  )

(logic)

(define-trusted-clause-processor
  SMT-trusted-cp
  nil
  :ttag Smtlink)
)

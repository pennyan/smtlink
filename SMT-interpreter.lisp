;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (13th March, 2014)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software


;;SMT-interpreter formats the results

(in-package "ACL2")
(include-book "SMT-run")
(include-book "config")
(include-book "std/io/read-string" :dir :system)
(include-book "tools/bstar" :dir :system)

(defttag :tshell)
(defttag :read-string)

(set-state-ok t)

;; SMT-interpreter
;; If failed, one needs to fire off a raw lisp session
;; and bind all variables with values.
;; Need to tell user informations on how to leave the
;; session.
;;
;; Changes included to bind counter example to global variable "cex" - Carl
(defun SMT-interpreter (filename smt-config state)
  "SMT-intepreter: get the result returned from calling SMT procedure"
  (b* (((mv exit-status lines) (SMT-run filename smt-config)))
    (cond
     ((not (equal exit-status 0))
      (mv (cw "Z3 failure: ~q0" lines) state))
     (t (if (equal (car lines) "proved")
            (b* ((cmd (concatenate 'string "rm -f " filename))
                 ((mv exit-status-rm lines-rm) (time$ (tshell-call cmd
                                                                   :print t
                                                                   :save t)
                                                      :msg "; rm -f: `~s0`: ~st sec, ~sa bytes~%"
                                                      :args (list cmd))))
              (if (equal exit-status-rm 0)
                  (mv t state)
                (mv (er hard? 'top-level "Error(SMT-interpreter): Remove file error.~% ~q0~%" lines-rm) state)))
          (b* 	(((mv err st state) (read-string (car lines)))
                 (- (cw "st:~q0" st))
                 (- (cw "err:~q0" err))
                 (state (f-put-global 'SMT-cex nil state))
                 (state (f-put-global 'SMT-cex (car st) state)))
            (mv (cw "~q0" lines) state)))
		))))

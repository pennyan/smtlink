;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (13th March, 2014)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software


(in-package "SMT")

(include-book "std/io/read-string" :dir :system)
(include-book "centaur/misc/tshell" :dir :system)
;; Proves f-put-global is returning state-p1
(include-book "system/f-put-global" :dir :system)

(include-book "../verified/SMT-hint-interface")

(defttag :tshell)
(value-triple (tshell-ensure))
(defttag :read-string)
(set-state-ok t)

;; (defsection SMT-run
;;   :parent (Smtlink)
;;  :short "SMT-run runs the configured SMT solver then interprets the result and feed it back to ACL2."

  (define SMT-run ((fname stringp) (smt-conf smtlink-config-p))
    :returns (mv (exit-status natp)
                 (lines string-listp))
    (let ((cmd (concatenate 'string (smtlink-config->smt-cmd smt-conf) " " fname)))
      (time$ (tshell-call cmd
                          :print t
                          :save t)
             :msg "; SMT solver: `~s0`: ~st sec, ~sa bytes~%"
             :args (list cmd))))

  ;; Changes included to bind counter example to global variable "cex" - Carl
(define SMT-interpret ((fname stringp) (smt-conf smtlink-config-p) (state))
  (declare (xargs :stobjs state))
    :returns (mv (proved? booleanp)
                 (state))
    :verify-guards nil
    (b* (((mv exit-status lines) (SMT-run fname smt-conf))
         ((unless (equal exit-status 0))
          (mv (er hard? 'SMT-run=>SMT-interpret "Z3 failure: ~q0" lines) state))
         ((if (equal lines nil))
          (mv (er hard? 'SMT-run=>SMT-interpret "Nothing returned from SMT solver.") state))
         ((if (equal (car lines) "proved"))
          (b* ((cmd (concatenate 'string "rm -f " fname))
               ((mv exit-status-rm lines-rm) (time$ (tshell-call cmd
                                                                 :print t
                                                                 :save t)
                                                    :msg "; rm -f: `~s0`: ~st sec, ~sa bytes~%"
                                                    :args (list cmd))))
            (if (equal exit-status-rm 0)
                (mv t state)
              (mv (er hard? 'SMT-run=>SMT-interpret "Remove file error.~% ~q0~%" lines-rm)
                  state))))
         ((mv err st state) (read-string (car lines) :state state))
         ((unless (true-listp st))
          (prog2$
           (er hard? 'SMT-run=>SMT-interpret "We can never prove anything about the thing returned by read-string. So we add a check for it. It's surprising that the check for true-listp failed: ~q0" st)
           (mv nil state)))
         (- (cw "st:~q0" st))
         (- (cw "err:~q0" err))
         (state (f-put-global 'SMT-cex nil state))
         (state (f-put-global 'SMT-cex (car st) state)))
      (mv (cw "~q0" lines) state)))

  (encapsulate ()
    (local
     (defthm endp-of-not-consp-of-string-listp
       (implies (and (string-listp x) (not (consp x)))
                (not x))
       :rule-classes nil)
     )

    (local
     (defthm stringp-of-consp-of-string-listp
       (implies (and (string-listp x) (consp x))
                (stringp (car x)))
       :rule-classes nil)
     )

    (verify-guards SMT-interpret :guard-debug t
      :hints (("goal"
               :in-theory (disable f-put-global)
               :use ((:instance endp-of-not-consp-of-string-listp (x (mv-nth 1 (smt-run fname smt-conf))))
                     (:instance stringp-of-consp-of-string-listp (x (mv-nth 1 (smt-run fname smt-conf))))))))
    )
  ;; )

(defttag nil)

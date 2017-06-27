;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (13th March, 2014)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software

(in-package "SMT")
(include-book "std/io/top" :dir :system)
(include-book "centaur/misc/tshell" :dir :system)

(include-book "z3-py/SMT-translator")

(defttag :tshell)
(value-triple (tshell-ensure))
(set-state-ok t)
(defttag :writes-okp)

(defsection SMT-write
  :parents (trusted)
  :short "SMT-write writes out the translated string to a SMT file as configured."

  (local (in-theory (enable characterp wordp)))
  (define princ$-paragraph ((par paragraphp) (channel symbolp) (state))
    (declare (xargs :guard (open-output-channel-p channel :character state)
                    :stobjs state))
    :returns (state)
    :hints (("Goal"
             :use ((:instance acl2-count-of-fixed-smaller (x par))
                   (:instance acl2-count-of-car-of-fixed-smaller (x par))
                   (:instance acl2-count-of-cdr-of-fixed-smaller (x par)))))
    :verify-guards nil
    (b* ((par (paragraph-fix par))
         (channel (symbol-fix channel))
         ((unless (consp par)) (if (equal par nil) state
                                 (princ$ par channel state)))
         ((cons first rest) par)
         (state (princ$-paragraph first channel state)))
      (princ$-paragraph rest channel state)))

  (defthm open-output-channel-p1-of-princ$-paragraph
    (implies (and (state-p1 state)
                  (symbolp channel)
                  (open-output-channel-p1 channel :character state))
             (let ((state (princ$-paragraph par channel state)))
               (and (state-p1 state)
                    (open-output-channel-p1 channel :character state))))
    :hints (("Goal" :in-theory (enable princ$-paragraph))))

  (verify-guards princ$-paragraph
    :hints (("Goal"
             :in-theory (enable paragraph-fix paragraphp)
             :use ((:instance equal-of-fixed-to-x (x par))))))

  (define SMT-write-file ((fname stringp) (acl22smt paragraphp) (smt-head paragraphp) (thm paragraphp) (state))
    :returns (state)
    (b* ((fname (str-fix fname))
         (acl22smt (paragraph-fix acl22smt))
         ((mv channel state) (open-output-channel! fname :character state))
         ((unless channel)
          (er hard? 'SMT-write=>SMT-write-file "Can't open file ~q0 as SMT file." fname)
          state)
         (state (princ$-paragraph acl22smt channel state))
         (state (princ$-paragraph smt-head channel state))
         (state (princ$-paragraph thm channel state)))
      (close-output-channel channel state)))
)


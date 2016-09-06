;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software
;;

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)


(defsection SMT-hint-interface
  :parents (Smtlink)
  :short "Define default Smtlink hint interface"

  ;; -------------------------------------------------------
  ;;
  ;; Define default Smtlink hint interface
  ;;
  ;;  One needs to attach to SMT-hint their own aggregate
  ;;    to pass in a different hint.
  ;;

  (defun list-fix (x)
    (declare (xargs :guard t))
    (if (listp x) x nil))

  (deffixtype list
    :fix list-fix
    :pred listp
    :equiv equal)

  (defprod hint-pair
    ((thm listp)       ;; a theorem statement about the variable
     (hints listp)     ;; the hint for proving this theorem
     ))

  (deflist hint-pair-list
    :elt-type hint-pair
    :pred hint-pair-listp
    :true-listp t)

  (defprod decl
    ((name symbolp)
     (type hint-pair-p)))

  (deflist decl-list
    :elt-type decl
    :pred decl-listp
    :true-listp t)

  (defprod func
    ((name symbolp)
     (formals decl-listp)
     (guard hint-pair-listp)
     (returns decl-listp)             ;; belong to auxiliary hypotheses
     (more-returns hint-pair-listp)   ;; belong ot auxiliary hypotheses
     (expansion-depth integerp)
     (uninterpreted booleanp)))

  (deflist func-list
    :elt-type func
    :pred func-listp
    :true-listp t)

  (defprod smtlink-hint
    ((functions func-listp)
     (hypotheses hint-pair-listp)
     (main-hint listp)
     (int-to-rat booleanp)
     (python-file stringp)
     (smt-hint listp)
     (aux-hint-list hint-pair-listp)
     (expanded-clause-w/-hint hint-pair-p)))

  (defconst *default-smtlink-hint*
    (make-smtlink-hint :functions nil
                       :hypotheses nil
                       :main-hint nil
                       :int-to-rat t
                       :python-file ""
                       :smt-hint nil
                       :aux-hint-list nil
                       :expanded-clause-w/-hint (make-hint-pair :thm nil :hints nil)))

  (defstub smt-hint () => *)

  (defun default-smtlink-hint ()
    (declare (xargs :guard t))
    (change-smtlink-hint *default-smtlink-hint*))

  (defattach smt-hint default-smtlink-hint)


  ;; -------------------------------------------------------------------------
  ;;        Define a set of utilities for conveniency

  ;; (defmacro def-smt-hint (name &key auto-expand))
  )

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

  (define pseudo-term-fix (x)
    :enabled t
    (if (pseudo-termp x) x nil))

  (deffixtype pseudo-term
    :fix pseudo-term-fix
    :pred pseudo-termp
    :equiv equal)

  (define pseudo-term-list-fix (x)
    :enabled t
    (if (pseudo-term-listp x) x nil))

  (deffixtype pseudo-term-list
    :fix pseudo-term-list-fix
    :pred pseudo-term-listp
    :equiv equal)

  (define list-fix (x)
    :enabled t
    (if (listp x) x nil))

  (deffixtype list
    :fix list-fix
    :pred listp
    :equiv equal)

  (defprod hint-pair
    ((thm pseudo-termp :default nil)       ;; a theorem statement about the variable
     (hints listp :default nil)     ;; the hint for proving this theorem
     ))

  (deflist hint-pair-list
    :elt-type hint-pair
    :pred hint-pair-listp
    :true-listp t)

  (defprod decl
    ((name symbolp :default nil)
     (type hint-pair-p :default (make-hint-pair))))

  (deflist decl-list
    :elt-type decl
    :pred decl-listp
    :true-listp t)

  (defprod func
    ((name symbolp :default nil)
     (formals decl-listp :default nil)
     (guard hint-pair-listp :default nil)
     (returns decl-listp :default nil)             ;; belong to auxiliary hypotheses
     (more-returns hint-pair-listp :default nil)   ;; belong ot auxiliary hypotheses
     (body pseudo-termp :default nil)
     (expansion-depth natp :default 0)
     (uninterpreted booleanp :default nil)))

  (deflist func-list
    :elt-type func
    :pred func-listp
    :true-listp t)

  (defalist func-alist
    :key-type symbol
    :val-type func
    :pred func-alistp)

  (defprod smtlink-hint
    ((functions func-listp :default nil)
     (hypotheses hint-pair-listp :default nil)
     (main-hint listp :default nil)
     (int-to-rat booleanp :default t)
     (python-file stringp :default "")
     (smt-hint listp :default nil)
     (fast-functions func-alistp :default nil)
     (aux-hint-list hint-pair-listp :default nil)
     (expanded-clause-w/-hint hint-pair-p :default (make-hint-pair))))

  (defconst *default-smtlink-hint*
    (make-smtlink-hint))

  (defstub smt-hint () => *)

  (define default-smtlink-hint ()
    (change-smtlink-hint *default-smtlink-hint*))

  (defattach smt-hint default-smtlink-hint)


  ;; -------------------------------------------------------------------------
  ;;        Define a set of utilities for conveniency

  ;; (defmacro def-smt-hint (name &key auto-expand))
  )

;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software
;;

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)

;; -------------------------------------------------------
;;
;; Define default Smtlink hint interface
;;
;;  One needs to attach to SMT-hint their own aggregate
;;    to pass in a different hint.
;;

(defprod hint-pair
  (thm symbolp
   hints listp))

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
   (formals decl-listp)             ;; belong to auxiliary hypotheses
   (guard hint-pair-listp)          ;; belong to auxiliary hypotheses
   (returns decl-listp)             ;; belong to auxiliary hypotheses
   (more-returns hint-pair-listp)   ;; belong ot auxiliary hypotheses
   (expansion-depth integerp)
   (uninterpreted booleanp)))

(deflist func-list
  :elt-type func
  :pred func-listp
  :true-listp t)

(defprod smtlink-hint
  (functions func-listp
   hypotheses hint-pair-listp
   hints listp
   int-to-rat booleanp
   python-file stringp))

(defconst *default-smtlink-hint*
  (make-smtlink-hint :functions nil
                     :hypotheses nil
                     :hints nil
                     :int-to-rat t
                     :python-file ""))

(defstub smt-hint () => *)

(defun default-smtlink-hint ()
  (declare (xargs :guard t))
  (change-smtlink-hint *default-smtlink-hint*))

(defattach smt-hint default-smtlink-hint)


;; -------------------------------------------------------------------------
;;        Define a set of utilities for conveniency

(defmacro def-smt-hint (name &key auto-expand))

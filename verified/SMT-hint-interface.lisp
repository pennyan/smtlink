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
;; Define default Smtlink hint
;;
;;  One needs to attach to SMT-hint their own aggregate
;;    to pass in a different hint.
;;

(defprod hints-pair
  (thm symbolp
   hints listp))

(deflist hints-pair-list
  :elt-type hints-pair
  :pred hints-pair-listp
  :true-listp t)


(defprod func
  (name symbolp
   type hints-pair-p
   level natp
   ))

(deflist func-list
  :elt-type func
  :pred func-listp
  :true-listp t)

(defprod uninterpreted
  (name symbolp
   input-types symbol-listp
   output-type hints-pair-p))

(deflist uninterpreted-list
  :elt-type uninterpreted
  :pred uninterpreted-listp
  :true-listp t)

(defprod smtlink-hint
  (expansions func-listp
   uninterpreted uninterpreted-listp
   hypotheses hints-pair-listp
   int-to-rat booleanp
   python-file stringp))

(defconst *default-smtlink-hint*
  (make-smtlink-hint :expansions nil
                     :uninterpreted nil
                     :hypotheses nil
                     :int-to-rat t
                     :python-file ""))

(defstub smt-hint () => *)

(defun default-smtlink-hint ()
  (declare (xargs :guard t))
  (change-smtlink-hint *default-smtlink-hint*))

(defattach smt-hint default-smtlink-hint)


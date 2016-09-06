;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (August 4th 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software


(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)


(defsection SMT-config
  :parents (Smtlink)
  :short "Define Smtlink config"

(defprod smtlink-config
  ((interface-dir stringp)
   (SMT-files-dir stringp)
   (SMT-module    stringp)
   (SMT-class     stringp)
   (SMT-cmd       stringp)
   (file-format   stringp)))

(defconst *default-smtlink-config*
  (make-smtlink-config :interface-dir "../z3_interface/"
                       :SMT-files-dir ""
                       :SMT-module "ACL2_to_Z3"
                       :SMT-class "ACL22SMT"
                       :SMT-cmd "/Users/penny/bin"
                       :file-format ".py"))

(defstub smt-cnf () => *)

(define default-smtlink-config ()
  (declare (xargs :guard t))
  (change-smtlink-config *default-smtlink-config*))

(defattach smt-cnf default-smtlink-config)

)

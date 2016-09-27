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
  ((interface-dir stringp :default "")
   (SMT-files-dir stringp :default "")
   (SMT-module    stringp :default "")
   (SMT-class     stringp :default "")
   (SMT-cmd       stringp :default "")
   (file-format   stringp :default "")))

(defconst *default-smtlink-config* (make-smtlink-config :interface-dir "" :SMT-files-dir "" :SMT-module "" :SMT-class "" :SMT-cmd "" :file-format ""))

(define smt-cnf ()
  :returns (smt-conf smtlink-config-p)
  *default-smtlink-config*)

)

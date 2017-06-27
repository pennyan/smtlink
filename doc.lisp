;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (June 26th 2017)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software
;;

(in-package "SMT")
(include-book "doc-tutorial")
(include-book "doc-dev")

;; ------------------------------------------------------- ;;
;;    Documentation

(include-book "xdoc/save" :dir :system)  ;; load xdoc::save

(defxdoc Smtlink
  :parents (ACL2::top)
  :short "Tutorial and documentation for the ACL2 book, Smtlink."
  :long "<h3>Introduction</h3>
         <p><b>Smtlink</b> is a tool for integrating external SMT solvers into ACL2.
         It is based on the @(see Clause-processor) mechanism.</p>
         <p>Under construction ...</p>")

(xdoc::save "./manual" :redef-okp t)  ;; write the manual

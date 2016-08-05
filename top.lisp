;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software
;;

(in-package "SMT")

(include-book "verified/SMT-verified-cp")
(include-book "verified/SMT-hint-wrapper")
(include-book "verified/Smtlink")
(include-book "verified/SMT-goal-generator")

(include-book "trusted/SMT-trusted-cp")

;; ------------------------------------------------------- ;;
;;    Documentation

;; (include-book "xdoc/save" :dir :system)  ;; load xdoc::save

;; (defxdoc acl2::top           ;; create a "top" topic
;;   :short "Tutorial and documentation for the ACL2 book, Smtlink."
;;   :long "<h3>Introduction</h3>
;;          <p><b>Smtlink</b> is a tool for integrating external SMT solvers into ACL2.
;;          It is based on the @(see Clause-processor) mechanism.</p>
;;          <p>Under construction ...</p>")

;; (xdoc::save "./Smtlink-manual")  ;; write the manual

;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software
;;

(in-package "SMT")

(include-book "verified/SMT-verified-cps")
(include-book "verified/SMT-computed-hints")
(include-book "verified/Smtlink")
(include-book "verified/SMT-goal-generator")
(include-book "verified/SMT-hint-interface")
(include-book "verified/SMT-config")
(include-book "verified/SMT-extractor")

(include-book "trusted/SMT-trusted-cp")
(include-book "trusted/SMT-prove")
(include-book "trusted/SMT-run")
(include-book "trusted/SMT-write")

(include-book "trusted/z3-py/SMT-names")
(include-book "trusted/z3-py/SMT-translator")
(include-book "trusted/z3-py/SMT-header")
(include-book "trusted/z3-py/ACL22SMT")

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

(xdoc::save "./Smtlink-manual" :redef-okp t)  ;; write the manual

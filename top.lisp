;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software
;;

(in-package "SMT")

;; verified
(include-book "verified/SMT-basics")
(include-book "verified/SMT-computed-hints")
(include-book "verified/SMT-config")
(include-book "verified/SMT-extractor")
(include-book "verified/SMT-goal-generator")
(include-book "verified/SMT-hint-interface")
(include-book "verified/SMT-hint-please")
(include-book "verified/SMT-verified-cps")
(include-book "verified/Smtlink")

;; trusted
(include-book "trusted/SMT-prove")
(include-book "trusted/SMT-run")
(include-book "trusted/SMT-trusted-cp")
(include-book "trusted/SMT-write")

;; trusted/z3-py
(include-book "trusted/z3-py/SMT-header")
(include-book "trusted/z3-py/SMT-names")
(include-book "trusted/z3-py/SMT-translator")



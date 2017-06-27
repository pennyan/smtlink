;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (June 26th 2017)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software
;;

(in-package "SMT")

(include-book "SMT-basics")
(include-book "SMT-extractor")
(include-book "SMT-verified-cps")
(include-book "SMT-computed-hints")
(include-book "SMT-goal-generator")
(include-book "Smtlink")
(include-book "SMT-hint-interface")
(include-book "SMT-config")
(include-book "SMT-hint-please")

;; ------------------------------------------------------- ;;
;;    Documentationc

(defxdoc verified
  :parents (Developer)
  :short ""
  :long "<h3>Introduction</h3>")

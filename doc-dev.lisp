;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (June 26th 2017)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software
;;

(in-package "SMT")
(include-book "verified/verified")
(include-book "trusted/trusted")


;; ------------------------------------------------------- ;;
;;    Documentation

(include-book "xdoc/save" :dir :system)  ;; load xdoc::save

(defxdoc Developer
  :parents (Smtlink)
  :short ""
  :long "<h3>Introduction</h3>")

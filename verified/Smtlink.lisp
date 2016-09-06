;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software
;;

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)


;; --------------------------------------------------------

(defmacro Smtlink (clause)
  `(Smtlink-subgoals ,clause
                     ;; A and G-prim and hints
                     (Smt-goal-generator ,clause (smt-hint))))

;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software
;;

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)

(include-book "SMT-hint-interface")

(defsection SMT-goal-generator
  :parents (Smtlink)
  :short "SMT-goal-generator generates the three type of goals for the verified
  clause processor"

  (define expand (term hints)
    :ignore-ok t
    :irrelevant-formals-ok t
    nil)

  (define generate-aux (fn-lst hp-lst)
    :ignore-ok t
    :irrelevant-formals-ok t
    nil)

  (define SMT-goal-generator (cl hints)
    :guard (smtlink-hint-p hints)
    (b* ((main-hint (smtlink-hint->hints hints))
         (fn-lst (smtlink-hint->functions hints))
         (hp-lst (smtlink-hint->hypotheses hints))
         (G-prim (expand cl fn-lst))
         (aux-&-hint-alist (generate-aux hp-lst fn-lst))
         (G-prim-and-main-hint `(,G-prim . ,main-hint))
         (SMT-hint `(:clause-processor (SMT-trusted-cp clause))))
      `(,aux-&-hint-alist ,G-prim-and-main-hint ,SMT-hint)))
  )

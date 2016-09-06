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
    term)

  (define generate-fn-hint-lst (fn-lst)
    :guard (func-listp fn-lst)
    :returns (fn-hint-lst hint-pair-listp)
    :ignore-ok t
    :irrelevant-formals-ok t

    nil
    )

  (define generate-hyp-hint-lst (hyp-lst)
    :guard (hint-pair-listp hyp-lst)
    :returns (hyp-hint-lst hint-pair-listp)
    :ignore-ok t
    :irrelevant-formals-ok t

    nil
    )

  (define SMT-goal-generator (cl hints)
    :guard (and (smtlink-hint-p hints)
                (pseudo-term-listp cl))
    :returns (new-hints smtlink-hint-p)

    (b* ((fn-lst (smtlink-hint->functions hints))
         (fn-hint-lst (generate-fn-hint-lst fn-lst))

         (hyp-lst (smtlink-hint->hypotheses hints))
         (hyp-hint-lst (generate-hyp-hint-lst hyp-lst))

         (total-aux-hint-lst `(,@(fn-hint-lst hyp-hint-lst)))

         (G-prim (expand (disjoin cl) fn-lst))
         (main-hint (smtlink-hint->main-hint hints))
         (expanded-clause-w/-hint `(G-prim . main-hint))
         (new-hints
          (change-smtlink-hint hints
                               :aux-hint-list total-aux-hint-lst
                               :expanded-clause-w/-hint expanded-clause-w/-hint
                               )))
      new-hints))
  )

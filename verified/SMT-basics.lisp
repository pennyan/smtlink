;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software
;;

(in-package "SMT")
(include-book "xdoc/top" :dir :system)

(defsection SMT-basics
  :parents (Smtlink)
  :short "Basic functions and types in Smtlink."

  (defconst *SMT-basics*
    (append
     '(rationalp realp booleanp integerp)
     '(binary-+ binary-* unary-/ unary--
                equal <
                implies if not
                lambda )))

  (defconst *SMT-functions*
    ;;(ACL2 function     . (SMT function         Least # of arguments))
    `((binary-+          . ("_SMT_.plus"       . 1))
      (binary-*          . ("_SMT_.times"      . 1))
      (unary-/           . ("_SMT_.reciprocal" . 1))
      (unary--           . ("_SMT_.negate"     . 1))
      (equal             . ("_SMT_.equal"      . 2))
      (<                 . ("_SMT_.lt"         . 2))
      (if                . ("_SMT_.ifx"        . 3))
      (not               . ("_SMT_.notx"       . 1))
      (lambda            . ("lambda"           . 2))
      (implies           . ("_SMT_.implies"    . 2))
      (hint-please       . ("_SMT_.hint_okay"  . 0))
      ;; This doesn't work right now because Z3's definition is different from ACL2
      ;; when using types as hypotheses. If X is rationalp in Z3, then it can not
      ;; be an integerp. We need to first grab a definition in Z3 that can fully
      ;; capture its ACL2 meaning.
      ;; (integerp      . ("_SMT_.integerp"   . 1))
      ;; (rationalp     . ("_SMT_.rationalp"  . 1))
      ;; (booleanp      . ("_SMT_.booleanp"   . 1))
      ))

  (defconst *SMT-types*
    ;;(ACL2 type      .  SMT type)
    `((realp          . "_SMT_.isReal")
      (rationalp      . "_SMT_.isReal")
      (integerp       . "_SMT_.isInt")
      (booleanp       . "_SMT_.isBool")))

  (defconst *SMT-uninterpreted-types*
    `((realp          . "_SMT_.R")
      (rationalp      . "_SMT_.R")
      (real/rationalp . "_SMT_.R")
      (integerp       . "_SMT_.Z")
      (booleanp       . "_SMT_.B")))
)

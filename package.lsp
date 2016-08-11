;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software
;;

(in-package "ACL2")

;; load other packages needed to define our new packages...
(include-book "std/portcullis" :dir :system)
(include-book "centaur/fty/portcullis" :dir :system)

;; define our new packages
(defpkg "SMT"
  (set-difference-eq
   (union-eq
    *acl2-exports*
    *standard-acl2-imports*
    *common-lisp-symbols-from-main-lisp-package*
    ;; Things we want to export
    '()
    ;; Things we want to import
    '(b*
      define
      defconsts
      tshell-ensure
      tshell-call
      set-raw-mode-on
      defxdoc
      defsection
      def-join-thms
      termify-clause-set

      conjoin-clauses
      conjoin
      conjoin2
      disjoin
      disjoin2
      disjoin-lst
      pseudo-term-list-listp
      iff-implies-equal-not
      split-keyword-alist
      dumb-negate-lit

      must-succeed

      prefixp

      str::cat
      str::natstr
      str::strtok
      str::count
      str::substrp
      str::isubstrp
      str::strpos
      str::firstn-chars
      str::strval
      str::search

      std::defaggregate

      fty::defprod
      fty::deflist
      )
    )
   ;; Things to remove
   '()))

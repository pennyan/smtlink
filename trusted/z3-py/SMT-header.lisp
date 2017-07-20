;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (26th September, 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software

(in-package "SMT")
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)

(include-book "SMT-translator")

(defsection SMT-header
  :parents (z3-py)
  :short "SMT-header contains string definitions for the header of a Z3 file."

  (local (in-theory (enable paragraphp wordp)))
  (define SMT-head ((smt-conf smtlink-config-p) (state))
    :guard (acl2::f-boundp-global 'acl2::system-books-dir state)
    :guard-debug t
    :returns (mv (head paragraphp)
                 (import paragraphp))
    :ignore-ok t
    (b* ((smt-conf (mbe :logic (smtlink-config-fix smt-conf) :exec smt-conf))
         ((smtlink-config c) smt-conf)
         (sys-dir (f-get-global 'acl2::system-books-dir state))
         ((unless (stringp sys-dir))
          (mv (er hard? 'SMT-header=>SMT-head "Failed to find where the system ~
  books are.") nil))
         (relative-smtlink-dir "smtlink/z3_interface")
         ;; (relative-smtlink-dir "../z3_interface")
         )
      (mv (list
           "from sys import path"
           #\Newline
           "path.insert(0,\"" sys-dir relative-smtlink-dir "\")"
           ;; "path.insert(0,\"" relative-smtlink-dir "\")"
           #\Newline
           "from " c.SMT-module " import *"
           #\Newline
           #\Newline)
          (list
           ;; "from " c.SMT-module " import " c.SMT-class
           #\Newline
           "_SMT_ = " c.SMT-class "()"
           #\Newline))))
  )

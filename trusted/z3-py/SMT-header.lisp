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
  :parent (Smtlink)
  :short "SMT-header contains string definitions for the header of a Z3 file."

  (define write-head ((conf smtlink-config-p))
    :returns (head paragraphp)
    (b* ((conf (mbe :logic (smtlink-config-fix conf) :exec conf))
         ((smtlink-config c) conf))
      (list "from sys import path"
            #\Newline
            "path.insert(0,\"" c.interface-dir "\")"
            #\Newline
            "from " c.SMT-module " import " c.SMT-class
            #\Newline
            "_SMT_ = " c.SMT-class "()"
            #\Newline)))
  )

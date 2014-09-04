;; This is a small exanple for connecting
;; verilog and ACL2,
;; Print the inner representation
;; and check equivalence of the two models

(in-package "ACL2")
(include-book "centaur/vl/top" :dir :system)
;; (include-book "tools/plev-ccl" :dir :system)

;; ;;these are from the acl2 books example
;; ;;not sure which one is also used
;; (include-book "centaur/4v-sexpr/top" :dir :system)
;; (include-book "centaur/misc/memory-mgmt" :dir :system)
;; (include-book "centaur/esim/stv/stv-top" :dir :system)
;; (include-book "centaur/esim/stv/stv-debug" :dir :system)
;; (include-book "centaur/gl/gl" :dir :system)
;; (include-book "centaur/aig/g-aig-eval" :dir :system)

;; (set-waterfall-parallelism nil)
;; (def-gl-clause-processor my-glcp)

;; (plev)

;; (set-slow-alist-action :break)
;; (set-debugger-enable t)
;; (break-on-error t)
;; (value-triple (set-max-mem (* 3 (expt 2 30))))

(defmodules *ACL2-circuit1*
    (vl::make-vl-loadconfig
     :start-files (list "circuit1.v")))

(defmodules *ACL2-circuit2*
    (vl::make-vl-loadconfig
     :start-files (list "circuit2.v")))

(defmodules *ACL2-circuit3*
    (vl::make-vl-loadconfig
     :start-files (list "circuit3.v")))

(defmodules *ACL2-circuit4*
    (vl::make-vl-loadconfig
     :start-files (list "circuit4.v")))

;; Try to print something about the
;; inner representation of circuit1
(vl::vl-ppcs-modulelist
 (vl::vl-translation->mods *ACL2-circuit1*))

(defconst *ACL2-circuit1-vl*
  (vl::vl-find-module "circuit1"
		      (vl::vl-translation->mods *ACL2-circuit1*)))

(vl::vl-ppcs-module *ACL2-circuit1-vl*)

(vl::vl-warnings-to-string (vl::vl-module->warnings *ACL2-circuit1-vl*))

;; both circuit1 and circuit4 are correct design
;; so they are equivalence

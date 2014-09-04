;; This program verifies three things about the real intent example:
;; http://www.techdesignforums.com/practice/technique/blindsided-by-a-glitch/
;; 1. When without glitchy input, the specification and implementation
;; are logically equivalent.
;; 2. When with glitchy input, the implementation will propagate glitches.
;; 3. There exists 2 correct implementations.
;; Yan 2014/08/12

(in-package "ACL2")
(include-book "centaur/vl/top" :dir :system)
;; (include-book "tools/plev-ccl" :dir :system)

;; ;;these are from the acl2 books example
;; ;;not sure which one is also used
;; (include-book "centaur/4v-sexpr/top" :dir :system)
;; (include-book "centaur/misc/memory-mgmt" :dir :system)
(include-book "centaur/esim/stv/stv-top" :dir :system)
(include-book "centaur/esim/stv/stv-debug" :dir :system)
(include-book "centaur/gl/gl" :dir :system)
;; (include-book "centaur/aig/g-aig-eval" :dir :system)

;; (set-waterfall-parallelism nil)
(def-gl-clause-processor my-glcp)

;; (plev)

;; (set-slow-alist-action :break)
;; (set-debugger-enable t)
;; (break-on-error t)
;; (value-triple (set-max-mem (* 3 (expt 2 30))))

(defmodules *ACL2-specAssign*
    (vl::make-vl-loadconfig
     :start-files (list "specAssign.v")))

(defmodules *ACL2-specIf*
    (vl::make-vl-loadconfig
     :start-files (list "specIf.v")))

(defmodules *ACL2-specCase*
    (vl::make-vl-loadconfig
     :start-files (list "specCase.v")))

(defmodules *ACL2-impl*
    (vl::make-vl-loadconfig
     :start-files (list "impl.v")))

(defmodules *ACL2-crctImpl-1*
    (vl::make-vl-loadconfig
     :start-files (list "crctImpl_1.v")))

(defmodules *ACL2-crctImpl-2*
    (vl::make-vl-loadconfig
     :start-files (list "crctImpl_2.v")))

;; Print information on specAssign
(vl::vl-ppcs-modulelist
 (vl::vl-design->mods
  (vl::vl-translation->good *ACL2-specAssign*)))

(defconst *ACL2-specAssign-vl*
  (vl::vl-find-module "specAssign"
		      (vl::vl-design->mods
		       (vl::vl-translation->good *ACL2-specAssign*))))

(vl::vl-ppcs-module *ACL2-specAssign-vl*)

(vl::vl-warnings-to-string (vl::vl-module->warnings *ACL2-specAssign-vl*))

;; Print information on implementation
(vl::vl-ppcs-modulelist
 (vl::vl-design->mods
  (vl::vl-translation->good *ACL2-impl*)))

(defconst *ACL2-impl-vl*
  (vl::vl-find-module "implRI"
		      (vl::vl-design->mods
		       (vl::vl-translation->good *ACL2-impl*))))

(vl::vl-ppcs-module *ACL2-impl-vl*)

(vl::vl-warnings-to-string (vl::vl-module->warnings *ACL2-impl-vl*))

;; Print information on crctImpl1
(vl::vl-ppcs-modulelist
 (vl::vl-design->mods
  (vl::vl-translation->good *ACL2-crctImpl-1*)))

(defconst *ACL2-crctImpl-1-vl*
  (vl::vl-find-module "crctImpl_1"
		      (vl::vl-design->mods
		       (vl::vl-translation->good *ACL2-crctImpl-1*))))

(vl::vl-ppcs-module *ACL2-crctImpl-1-vl*)

(vl::vl-warnings-to-string (vl::vl-module->warnings *ACL2-crctImpl-1-vl*))

;; Print information on crctImpl2
(vl::vl-ppcs-modulelist
 (vl::vl-design->mods
  (vl::vl-translation->good *ACL2-crctImpl-2*)))

(defconst *ACL2-crctImpl-2-vl*
  (vl::vl-find-module "crctImpl_2"
		      (vl::vl-design->mods
		       (vl::vl-translation->good *ACL2-crctImpl-2*))))

(vl::vl-ppcs-module *ACL2-crctImpl-2-vl*)

(vl::vl-warnings-to-string (vl::vl-module->warnings *ACL2-crctImpl-2-vl*))

;; Use symbolic STV for checking equivalence
(defconst *specAssign*
  (vl::vl-module->esim *ACL2-specAssign-vl*))

(defconst *impl*
  (vl::vl-module->esim *ACL2-impl-vl*))

(defconst *crctImpl-1*
  (vl::vl-module->esim *ACL2-crctImpl-1-vl*))

(defconst *crctImpl-2*
  (vl::vl-module->esim *ACL2-crctImpl-2-vl*))

;; define test-vector
(defstv test-vector-specAssign
    :mod *specAssign*
    :inputs
    '(("dataA" dataA)
      ("dataB" dataB)
      ("a0" a0)
      ("sel" sel))
    :outputs
    '(("mux_out" mux_out)))
(defstv test-vector-impl
    :mod *impl*
    :inputs
    '(("dataA" dataA)
      ("dataB" dataB)
      ("a0" a0)
      ("sel" sel))
    :outputs
    '(("mux_out" mux_out)))

(defstv test-vector-specAssign-X
    :mod *specAssign*
    :inputs
    '(("dataA" _)
      ("dataB" _)
      ("a0" a0)
      ("sel" sel))
    :outputs
    '(("mux_out" mux_out)))
(defstv test-vector-impl-X
    :mod *impl*
    :inputs
    '(("dataA" _)
      ("dataB" _)
      ("a0" a0)
      ("sel" sel))
    :outputs
    '(("mux_out" mux_out)))
(defstv test-vector-crctImpl-1-X
    :mod *crctImpl-1*
    :inputs
    '(("dataA" _)
      ("dataB" _)
      ("a0" a0)
      ("sel" sel))
    :outputs
    '(("mux_out" mux_out)))
(defstv test-vector-crctImpl-2-X
    :mod *crctImpl-2*
    :inputs
    '(("dataA" _)
      ("dataB" _)
      ("a0" a0)
      ("sel" sel))
    :outputs
    '(("mux_out" mux_out)))

;; test stv-run
(stv-run (test-vector-specAssign)
	 '((dataA . 1)
	   (dataB . 0)
	   (a0 . 0)
	   (sel . 1)))
(stv-run (test-vector-impl)
	 '((dataA . 1)
	   (dataB . 0)
	   (a0 . 0)
	   (sel . 1)))
(stv-run (test-vector-specAssign)
	 '((dataA . 1)
	   (dataB . X)
	   (a0 . 0)
	   (sel . 0)))
(stv-run (test-vector-impl)
	 '((dataA . 1)
	   (dataB . X)
	   (a0 . 0)
	   (sel . 1)))

(stv-run (test-vector-specAssign-X)
	 '((a0 . 1)
	   (sel . 0)))
(stv-run (test-vector-impl-X)
	 '((a0 . 1)
	   (sel . 0)))
(stv-run (test-vector-crctImpl-1-X)
	 '((a0 . 1)
	   (sel . 0)))
(stv-run (test-vector-crctImpl-2-X)
	 '((a0 . 1)
	   (sel . 0)))

;; when without x inputs, should produce equivalence
(def-gl-thm spec-impl-equivalence-without-x
  :hyp (and (unsigned-byte-p 1 dataA)
            (unsigned-byte-p 1 dataB)
            (unsigned-byte-p 1 a0)
	    (unsigned-byte-p 1 sel))
  :concl (let* ((in-alist (list (cons 'dataA dataA)
                                (cons 'dataB dataB)
                                (cons 'a0  a0)
				(cons 'sel sel)))
                (out-alist1 (stv-run (test-vector-specAssign) in-alist))
                (res1 (cdr (assoc 'mux_out out-alist1)))
		(out-alist2 (stv-run (test-vector-impl) in-alist))
		(res2 (cdr (assoc 'mux_out out-alist2))))
           (equal res1 res2))
  :g-bindings (gl::auto-bindings
	       (:nat dataA 1)
	       (:nat dataB 1)
	       (:nat a0 1)
	       (:nat sel 1))
  :rule-classes nil)

;; when with x inputs, should produce none equivalence
(def-gl-thm spec-impl-equivalence-with-x
    :hyp (and (unsigned-byte-p 1 a0)
	      (unsigned-byte-p 1 sel))
    :concl (let* ((in-alist (list (cons 'a0  a0)
				  (cons 'sel sel)))
		  (out-alist1 (stv-run (test-vector-specAssign-X) in-alist))
		  (res1 (cdr (assoc 'mux_out out-alist1)))
		  (out-alist2 (stv-run (test-vector-impl-X) in-alist))
		  (res2 (cdr (assoc 'mux_out out-alist2))))
	     (equal res1 res2))
    :g-bindings (gl::auto-bindings
		 (:nat a0 1)
		 (:nat sel 1))
    :rule-classes nil)

(def-gl-thm spec-impl-equivalence-with-x-try-spec
    :hyp (and (unsigned-byte-p 1 a0)
	      (unsigned-byte-p 1 sel)
	      (let* ((in-alist (list (cons 'a0  a0)
				     (cons 'sel sel)))
		     (out-alist1 (stv-run (test-vector-specAssign-X) in-alist))
		     (res1 (cdr (assoc 'mux_out out-alist1))))
		(or (equal res1 1) (equal res1 0))))
    :concl (let* ((in-alist (list (cons 'a0  a0)
				  (cons 'sel sel)))
		  (out-alist1 (stv-run (test-vector-specAssign-X) in-alist))
		  (res1 (cdr (assoc 'mux_out out-alist1)))
		  (out-alist2 (stv-run (test-vector-impl-X) in-alist))
		  (res2 (cdr (assoc 'mux_out out-alist2))))
	     (equal res1 res2))
    :g-bindings (gl::auto-bindings
		 (:nat a0 1)
		 (:nat sel 1))
    :rule-classes nil)

(def-gl-thm spec-impl-equivalence-with-x-try-spec-more-ce
    :hyp (and (unsigned-byte-p 1 a0)
	      (unsigned-byte-p 1 sel)
	      (let* ((in-alist (list (cons 'a0  a0)
				     (cons 'sel sel)))
		     (out-alist1 (stv-run (test-vector-specAssign-X) in-alist))
		     (res1 (cdr (assoc 'mux_out out-alist1))))
		(or (equal res1 1) (equal res1 0)))
	      (not (and (equal a0 1)
			(equal sel 0))))
    :concl (let* ((in-alist (list (cons 'a0  a0)
				  (cons 'sel sel)))
		  (out-alist1 (stv-run (test-vector-specAssign-X) in-alist))
		  (res1 (cdr (assoc 'mux_out out-alist1)))
		  (out-alist2 (stv-run (test-vector-impl-X) in-alist))
		  (res2 (cdr (assoc 'mux_out out-alist2))))
	     (equal res1 res2))
    :g-bindings (gl::auto-bindings
		 (:nat a0 1)
		 (:nat sel 1))
    :rule-classes nil)

;; when with x inputs, should produce equivalence for crctImpl_1
(def-gl-thm spec-crctImpl-1-equivalence-with-x
    :hyp (and (unsigned-byte-p 1 a0)
	      (unsigned-byte-p 1 sel)
	      (let* ((in-alist (list (cons 'a0  a0)
				     (cons 'sel sel)))
		     (out-alist1 (stv-run (test-vector-specAssign-X) in-alist))
		     (res1 (cdr (assoc 'mux_out out-alist1))))
		(or (equal res1 1) (equal res1 0))))
    :concl (let* ((in-alist (list (cons 'a0  a0)
				  (cons 'sel sel)))
		  (out-alist1 (stv-run (test-vector-specAssign-X) in-alist))
		  (res1 (cdr (assoc 'mux_out out-alist1)))
		  (out-alist2 (stv-run (test-vector-crctImpl-1-X) in-alist))
		  (res2 (cdr (assoc 'mux_out out-alist2))))
	     (equal res1 res2))
    :g-bindings (gl::auto-bindings
		 (:nat a0 1)
		 (:nat sel 1))
    :rule-classes nil)

;; when with x inputs, should produce equivalence for crctImpl_2

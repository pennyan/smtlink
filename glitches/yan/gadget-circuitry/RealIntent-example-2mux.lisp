;; This program verifies three things about the real intent example:
;; http://www.techdesignforums.com/practice/technique/blindsided-by-a-glitch/
;; 1. When without glitchy input, the specification and implementation
;; are logically equivalent.
;; 2. When with glitchy input, the implementation will propagate glitches.
;; 3. There exists 2 correct implementations.
;; Yan 2014/08/12
;; Added a gadget for printing out ACL2 values for dataA and dataB

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

(defmodules *ACL2-specAssign-2mux*
    (vl::make-vl-loadconfig
     :start-files (list "specAssign_2mux.v")))

(defmodules *ACL2-impl-2mux*
    (vl::make-vl-loadconfig
     :start-files (list "impl_2mux.v")))

(defmodules *ACL2-crctImpl-1-2mux*
    (vl::make-vl-loadconfig
     :start-files (list "crctImpl_1_2mux.v")))

(defmodules *ACL2-crctImpl-2-2mux*
    (vl::make-vl-loadconfig
     :start-files (list "crctImpl_2_2mux.v")))

;; Print information on specAssign
(vl::vl-ppcs-modulelist
 (vl::vl-design->mods
  (vl::vl-translation->good *ACL2-specAssign-2mux*)))

(defconst *ACL2-specAssign-2mux-vl*
  (vl::vl-find-module "specAssign_2mux"
		      (vl::vl-design->mods
		       (vl::vl-translation->good *ACL2-specAssign-2mux*))))

(vl::vl-ppcs-module *ACL2-specAssign-2mux-vl*)

(vl::vl-warnings-to-string (vl::vl-module->warnings *ACL2-specAssign-2mux-vl*))

;; Print information on implementation
(vl::vl-ppcs-modulelist
 (vl::vl-design->mods
  (vl::vl-translation->good *ACL2-impl-2mux*)))

(defconst *ACL2-impl-2mux-vl*
  (vl::vl-find-module "implRI_2mux"
		      (vl::vl-design->mods
		       (vl::vl-translation->good *ACL2-impl-2mux*))))

(vl::vl-ppcs-module *ACL2-impl-2mux-vl*)

(vl::vl-warnings-to-string (vl::vl-module->warnings *ACL2-impl-2mux-vl*))

;; Print information on crctImpl1
(vl::vl-ppcs-modulelist
 (vl::vl-design->mods
  (vl::vl-translation->good *ACL2-crctImpl-1-2mux*)))

(defconst *ACL2-crctImpl-1-2mux-vl*
  (vl::vl-find-module "crctImpl_1_2mux"
		      (vl::vl-design->mods
		       (vl::vl-translation->good *ACL2-crctImpl-1-2mux*))))

(vl::vl-ppcs-module *ACL2-crctImpl-1-2mux-vl*)

(vl::vl-warnings-to-string (vl::vl-module->warnings *ACL2-crctImpl-1-2mux-vl*))

;; Print information on crctImpl2
(vl::vl-ppcs-modulelist
 (vl::vl-design->mods
  (vl::vl-translation->good *ACL2-crctImpl-2-2mux*)))

(defconst *ACL2-crctImpl-2-2mux-vl*
  (vl::vl-find-module "crctImpl_2_2mux"
		      (vl::vl-design->mods
		       (vl::vl-translation->good *ACL2-crctImpl-2-2mux*))))

(vl::vl-ppcs-module *ACL2-crctImpl-2-2mux-vl*)

(vl::vl-warnings-to-string (vl::vl-module->warnings *ACL2-crctImpl-2-2mux-vl*))

;; Use symbolic STV for checking equivalence
(defconst *specAssign-2mux*
  (vl::vl-module->esim *ACL2-specAssign-2mux-vl*))

(defconst *impl-2mux*
  (vl::vl-module->esim *ACL2-impl-2mux-vl*))

(defconst *crctImpl-1-2mux*
  (vl::vl-module->esim *ACL2-crctImpl-1-2mux-vl*))

(defconst *crctImpl-2-2mux*
  (vl::vl-module->esim *ACL2-crctImpl-2-2mux-vl*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; define test-vector
(defstv test-vector-specAssign-2mux
    :mod *specAssign-2mux*
    :inputs
    '(("xx" X)
      ("tt" 1)
      ("ff" 0)
      ("dataA_1" dataA_1)
      ("dataA_2" dataA_2)
      ("dataB" dataB)
      ("a0" a0)
      ("sel" sel))
    :outputs
    '(("mux_out" mux_out)))
(defstv test-vector-impl-2mux
    :mod *impl-2mux*
    :inputs
    '(("xx" X)
      ("tt" 1)
      ("ff" 0)
      ("dataA_1" dataA_1)
      ("dataA_2" dataA_2)
      ("dataB" dataB)
      ("a0" a0)
      ("sel" sel))
    :outputs
    '(("mux_out" mux_out)))
(defstv test-vector-crctImpl-1-2mux
    :mod *crctImpl-1-2mux*
    :inputs
    '(("xx" X)
      ("tt" 1)
      ("ff" 0)
      ("dataA_1" dataA_1)
      ("dataA_2" dataA_2)
      ("dataB" dataB)
      ("a0" a0)
      ("sel" sel))
    :outputs
    '(("mux_out" mux_out)))
(defstv test-vector-crctImpl-2-2mux
    :mod *crctImpl-2-2mux*
    :inputs
    '(("xx" X)
      ("tt" 1)
      ("ff" 0)
      ("dataA_1" dataA_1)
      ("dataA_2" dataA_2)
      ("dataB" dataB)
      ("a0" a0)
      ("sel" sel))
    :outputs
    '(("mux_out" mux_out)))

;; ;; test stv-run
;; (stv-run (test-vector-specAssign)
;; 	 '((dataA . 1)
;; 	   (dataB . 0)
;; 	   (a0 . 0)
;; 	   (sel . 1)))
;; (stv-run (test-vector-impl)
;; 	 '((dataA . 1)
;; 	   (dataB . 0)
;; 	   (a0 . 0)
;; 	   (sel . 1)))
;; (stv-run (test-vector-specAssign)
;; 	 '((dataA . 1)
;; 	   (dataB . X)
;; 	   (a0 . 0)
;; 	   (sel . 0)))
;; (stv-run (test-vector-impl)
;; 	 '((dataA . 1)
;; 	   (dataB . X)
;; 	   (a0 . 0)
;; 	   (sel . 1)))

;; (stv-run (test-vector-specAssign-X)
;; 	 '((a0 . 1)
;; 	   (sel . 0)))
;; (stv-run (test-vector-impl-X)
;; 	 '((a0 . 1)
;; 	   (sel . 0)))
;; (stv-run (test-vector-crctImpl-1-X)
;; 	 '((a0 . 1)
;; 	   (sel . 0)))
;; (stv-run (test-vector-crctImpl-2-X)
;; 	 '((a0 . 1)
;; 	   (sel . 0)))

;; when without x inputs, should produce equivalence
;; (def-gl-thm spec-impl-equivalence-without-x
;;   :hyp (and (unsigned-byte-p 1 dataA_1)
;; 	    (unsigned-byte-p 1 dataA_2)
;;             (unsigned-byte-p 1 dataB)
;;             (unsigned-byte-p 1 a0)
;; 	    (unsigned-byte-p 1 sel))
;;   :concl (let* ((in-alist (list (cons 'dataA_1 dataA_1)
;; 				(cons 'dataA_2 dataA_2)
;;                                 (cons 'dataB dataB)
;;                                 (cons 'a0  a0)
;; 				(cons 'sel sel)))
;;                 (out-alist1 (stv-run (test-vector-specAssign-2mux) in-alist))
;;                 (res1 (cdr (assoc 'mux_out out-alist1)))
;; 		(out-alist2 (stv-run (test-vector-impl-2mux) in-alist))
;; 		(res2 (cdr (assoc 'mux_out out-alist2))))
;;            (equal res1 res2))
;;   :g-bindings (gl::auto-bindings
;; 	       (:nat dataA_1 1)
;; 	       (:nat dataA_2 1)
;; 	       (:nat dataA 1)
;; 	       (:nat dataB 1)
;; 	       (:nat a0 1)
;; 	       (:nat sel 1))
;;   :rule-classes nil)

(def-gl-thm spec-impl-equivalence-with-x-try-spec
    :hyp (and (unsigned-byte-p 1 dataA_1)
	      (unsigned-byte-p 1 dataA_2)
	      (unsigned-byte-p 1 dataB)
	      (unsigned-byte-p 1 a0)
	      (unsigned-byte-p 1 sel)
	      (let* ((in-alist (list (cons 'dataA_1 dataA_1)
				     (cons 'dataA_2 dataA_2)
				     (cons 'dataB dataB)
				     (cons 'a0  a0)
				     (cons 'sel sel)))
		     (out-alist1 (stv-run (test-vector-specAssign-2mux) in-alist))
		     (res1 (cdr (assoc 'mux_out out-alist1))))
		(or (equal res1 1) (equal res1 0))))
    :concl (let* ((in-alist (list (cons 'dataA_1 dataA_1)
				  (cons 'dataA_2 dataA_2)
				  (cons 'dataB dataB)
				  (cons 'a0  a0)
				  (cons 'sel sel)))
		  (out-alist1 (stv-run (test-vector-specAssign-2mux) in-alist))
		  (res1 (cdr (assoc 'mux_out out-alist1)))
		  (out-alist2 (stv-run (test-vector-impl-2mux) in-alist))
		  (res2 (cdr (assoc 'mux_out out-alist2))))
	     (equal res1 res2))
    :g-bindings (gl::auto-bindings
		 (:nat dataA_1 1)
		 (:nat dataA_2 1)
		 (:nat dataB 1)
		 (:nat a0 1)
		 (:nat sel 1))
    :rule-classes nil)

;; when with x inputs, should produce equivalence for crctImpl_1
(def-gl-thm spec-crctImpl-1-equivalence-with-x
    :hyp (and (unsigned-byte-p 1 dataA_1)
	      (unsigned-byte-p 1 dataA_2)
	      (unsigned-byte-p 1 dataB)
	      (unsigned-byte-p 1 a0)
	      (unsigned-byte-p 1 sel)
	      (let* ((in-alist (list (cons 'dataA_1 dataA_1)
				     (cons 'dataA_2 dataA_2)
        			     (cons 'dataB dataB)
				     (cons 'a0  a0)
				     (cons 'sel sel)))
		     (out-alist1 (stv-run (test-vector-specAssign-2mux) in-alist))
		     (res1 (cdr (assoc 'mux_out out-alist1))))
		(or (equal res1 1) (equal res1 0))))
    :concl (let* ((in-alist (list (cons 'dataA_1 dataA_1)
				  (cons 'dataA_2 dataA_2)
	        		  (cons 'dataB dataB)
				  (cons 'a0  a0)
				  (cons 'sel sel)))
		  (out-alist1 (stv-run (test-vector-specAssign-2mux) in-alist))
		  (res1 (cdr (assoc 'mux_out out-alist1)))
		  (out-alist2 (stv-run (test-vector-crctImpl-1-2mux) in-alist))
		  (res2 (cdr (assoc 'mux_out out-alist2))))
	     (equal res1 res2))
    :g-bindings (gl::auto-bindings
		 (:nat dataA_1 1)
		 (:nat dataA_2 1)
		 (:nat dataB 1)
		 (:nat a0 1)
		 (:nat sel 1))
    :rule-classes nil)

;; when with x inputs, should produce equivalence for crctImpl_2

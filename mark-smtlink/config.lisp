;; This file configs the path to below directories:
;; 1. Z3_interface
;; 2. Z3_files
;; 3. name of z3 class
;; 4. SMT command

(in-package "ACL2")
(defconst *dir-interface* "/Users/mrg/src/smtlink/smtlink/z3\_interface")  ;; mrg
(defconst *dir-files* "z3\_files")
;; (defconst *z3-module* "ACL2\_translator") ;; mrg changed to use my subclass
(defconst *z3-module* "RewriteExpt")
;; (defconst *z3-class* "to_smt")
(defconst *z3-class* "to_smt_w_expt")
(defconst *smt-cmd* "python")
(defconst *dir-expanded* "expanded")

;; This file configs the path to below directories:
;; 1. Z3_interface
;; 2. Z3_files
;; 3. name of z3 class
;; 4. SMT command
(in-package "ACL2")
(include-book "std/util/defaggregate" :dir :system)

(std::defaggregate smtlink-config
  (dir-interface
   dir-files
   SMT-module
   SMT-class
   smt-cmd
   dir-expanded)
  :tag :smtlink-config)

(defconst *default-smtlink-config*
  (make-smtlink-config :dir-interface ""
		       :dir-files "z3\_files"
		       :SMT-module "ACL22SMT"
		       :SMT-class "to_smt"
		       :smt-cmd "python"
		       :dir-expanded  "expanded"))

(encapsulate
  (((smt-cnf) => *))
  (local (defun smt-cnf ()
	   *default-smtlink-config*)))

(defun default-smtlink-config ()
  (declare (xargs :guard t))
  (change-smtlink-config *default-smtlink-config*))

(defattach smt-cnf default-smtlink-config)

;; (defconst *dir-interface* "/ubc/cs/home/y/yanpeng/project/ACL2/smtlink/z3\_interface")
;; (defconst *dir-files* "z3\_files")
;; (defconst *z3-module* "ACL22SMT")
;; (defconst *z3-class* "to_smt")
;; (defconst *smt-cmd* "python")
;; (defconst *dir-expanded* "expanded")

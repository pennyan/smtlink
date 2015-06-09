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
  (make-smtlink-config :dir-interface nil
                       :dir-files "z3\_files"
                       :SMT-module "ACL2_to_Z3"
                       :SMT-class "ACL22SMT"
                       :smt-cmd "python"
                       :dir-expanded nil))

(encapsulate
  (((smt-cnf) => *))
  (local (defun smt-cnf ()
	   *default-smtlink-config*)))

(defun default-smtlink-config ()
  (declare (xargs :guard t))
  (change-smtlink-config *default-smtlink-config*))

(defattach smt-cnf default-smtlink-config)

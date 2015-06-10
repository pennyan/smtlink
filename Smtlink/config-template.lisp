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

;; Insert-code-for-default-smtlink-config

(encapsulate
  (((smt-cnf) => *))
  (local (defun smt-cnf ()
	   *default-smtlink-config*)))

(defun default-smtlink-config ()
  (declare (xargs :guard t))
  (change-smtlink-config *default-smtlink-config*))

(defattach smt-cnf default-smtlink-config)

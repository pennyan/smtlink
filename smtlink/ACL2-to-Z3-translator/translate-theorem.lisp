;; translate-theorem contains functions for translating a SMT-formula theorem into a Z3 theorem.
;; The construction is really very trivial since we extract out hypothesis and conclusion. 
(in-package "ACL2")

;; translate-theorem
(defun translate-theorem ()
  "translate-theorem: construct a theorem statement for Z3"
  (list "prove(Implies(hypothesis, conclusion))" #\Newline))



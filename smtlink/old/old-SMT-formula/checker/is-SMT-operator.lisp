;; is-SMT-operator contains functions checking if an operator is a SMT operator
(in-package "ACL2")

(include-book "is-SMT-arithmetic")
(include-book "is-SMT-logic")
(include-book "is-SMT-comparison")
(include-book "is-SMT-function-existing")

;; is-SMT-operator
(defun is-SMT-operator (opr)
  "is-SMT-operator: check if this is a SMT operator"
  (if (or (is-SMT-arithmetic opr) 
	  (is-SMT-logic opr) 
	  (is-SMT-comparison opr) 
	  (is-SMT-function-existing opr))
      t
    nil))

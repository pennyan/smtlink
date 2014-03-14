;; SMT-operator contains function for constructing SMT operators
(in-package "ACL2")
(include-book "../checker/is-SMT-arithmetic")
(include-book "SMT-arithmetic")
(include-book "../checker/is-SMT-logic")
(include-book "SMT-logic")
(include-book "../checker/is-SMT-comparison")
(include-book "SMT-comparison")
(include-book "SMT-function")

;; SMT-operator
(defun SMT-operator (opr)
  "SMT-operator: construct a SMT operator"
  (cond ((is-SMT-arithmetic opr) (SMT-arithmetic opr))
	((is-SMT-logic opr) (SMT-logic opr))
	((is-SMT-comparison opr) (SMT-comparison opr))
	(t (SMT-fun-name opr))))

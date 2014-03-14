;; translate-operator contains function for translating a SMT operator into Z3 operator
(in-package "ACL2")
(include-book "../SMT-formula/checker/is-SMT-arithmetic")
(include-book "translate-arithmetic")
(include-book "../SMT-formula/checker/is-SMT-logic")
(include-book "translate-logic")
(include-book "../SMT-formula/checker/is-SMT-comparison")
(include-book "translate-comparison")
(include-book "translate-function-exist")

;; translate-operator
(defun translate-operator (opr)
  "translate-operator: translate a SMT operator into Z3 operator"
  (cond ((is-SMT-arithmetic opr) (translate-arithmetic opr))
	((is-SMT-logic opr) (translate-logic opr))
	((is-SMT-comparison opr) (translate-comparison opr))
	(t (translate-function-exist opr))))

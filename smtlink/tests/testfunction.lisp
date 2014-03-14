(in-package "ACL2")

(defun simpleFun3 ()
  1)
(defun simpleFun2 (x)
  (* x x))#|ACL2s-ToDo-Line|#


;; 2x^3 - x*y > 0
(defun simpleFun (x y)
  (- (* 2 (simpleFun2 x) *simpleConst*) (* (simpleFun3) x y)))
;; Test cases for testing function expansion

;; 1. Define several test function
(defun foo (a b)
  (+ a b))
(defun bar (a b c d)
  (- (* c (foo a b)) d))


;; SMT-number contains the function for constructing and identifying literal numbers
(in-package "ACL2")

;; SMT-number
(defun SMT-number (number)
  "SMT-number: This is a SMT number"
  (if (or (rationalp number) (integerp number))
      number
    (cw "Error: This is not a valid SMT number: ~q0" number)))

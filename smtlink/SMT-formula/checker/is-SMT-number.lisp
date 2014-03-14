;; is-SMT-number contains the function for constructing and identifying literal numbers
(in-package "ACL2")

;; is-SMT-number
(defun is-SMT-number (number)
  "is-SMT-number: Check if this is a SMT number"
  (if (or (rationalp number) (integerp number)) t nil))


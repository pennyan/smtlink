;; helper functions for basic data structure manipulation
(in-package "ACL2")

;; my-last
(defun my-last (listx)
 "my-last: fetch the last element from list"
  (car (last listx)))

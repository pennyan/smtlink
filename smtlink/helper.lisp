;; helper functions for basic data structure manipulation
(in-package "ACL2")

;; my-last
(defun my-last (listx)
 "my-last: fetch the last element from list"
  (car (last listx)))

;; my-delete
(defun my-delete (listx elem)
  "my-delete: delete an element from the list. If there're duplicates, this function deletes the first one in the list."
  (if (endp listx) ;; elem does not exist in the list
      listx
      (if (equal (car listx) elem)
	  (cdr listx)
	  (cons (car listx)
		(my-delete (cdr listx) elem)))))

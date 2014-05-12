;; helper functions for basic data structure manipulation
(in-package "ACL2")

;; exist
(defun exist (elem lista)
  "exist: check if an element exist in a list"
  (if (endp lista)
      nil
    (if (equal elem (car lista))
	t
      (exist elem (cdr lista)))))

;; end
(defun end (lista)
  "end: return the last element in a list"
  (if (endp (cdr lista))
      (car lista)
    (end (cdr lista))))

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

(defthm delete-must-reduce
    (implies (exist a listx)
	     (< (len (my-delete listx a)) (len listx))))

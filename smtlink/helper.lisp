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

;; append-and
(defun append-and (listx listy)
  "append-and: append two and lists together in the underneath representation"
  (if (endp listy)
      listx
      (list 'if listx listy 'nil)))

;; assoc-no-repeat
(defun assoc-no-repeat (assoc-list)
  "assoc-no-repeat: check if an associate list has repeated keys"
  (if (endp assoc-list)
      t
      (if (equal (assoc (caar assoc-list) (cdr assoc-list)) nil)
	  (assoc-no-repeat (cdr assoc-list))
	  nil)))

;; invert-assoc
(defun invert-assoc (assoc-list)
  "invert-assoc: invert the key and value pairs in an associate list"
  (if (endp assoc-list)
      nil
      (cons (list (cadr (car assoc-list)) (car (car assoc-list)))
	   (invert-assoc (cdr assoc-list)))))

;; create-assoc-helper
 (defun create-assoc-helper (list-keys list-values)
   (if (endp list-keys)
       nil
       (cons (list (car list-keys) (car list-values))
	     (create-assoc-helper (cdr list-keys) (cdr list-values)))))

;; create-assoc
(defun create-assoc (list-keys list-values)
  "create-assoc: combines two lists together to form an associate list"
  (if (equal (len list-keys) (len list-values))
      (create-assoc-helper list-keys list-values)
      (cw "Error(helper): list-keys and list-values should be of the same len.")))

;; replace-lambda-params
 (defun replace-lambda-params (expr lambda-params-mapping)
   "replace-lambda-params: replace params in the expression using the mapping"
   (if (atom expr)
       (let ((res (assoc expr lambda-params-mapping)))
	 (if (equal res nil)
	     expr
	     (cadr res)))
       (cons (replace-lambda-params (car expr) lambda-params-mapping)
	     (replace-lambda-params (cdr expr) lambda-params-mapping))))

;; assoc-lambda
(defun assoc-lambda (expr lambda-params-mapping assoc-list)
  "assoc-lambda: replacing params in expression using lambda-params-mapping \
and check if the resulting term exist in assoc-list keys. Return the resulting \
pair from assoc-list."
  (b* ((new-expr (replace-lambda-params expr lambda-params-mapping))
       (final-res (assoc new-expr assoc-list)))
      final-res)
  )

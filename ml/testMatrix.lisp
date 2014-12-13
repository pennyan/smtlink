;; This is a test file for matrix operations in ACL2.

(in-package "ACL2")

;; set current book directory to the acl2 book directory
:set-cbd "/ubc/cs/research/isd/users/software/ACL2/acl2-sources/books"

;; set up directories to book
;;     books/workshops/2003/cowles-gamboa-van-baalen_matrix/
;; and books/workshops/2003/hendrix
(encapsulate ()
  (add-include-book-dir :matrix "workshops/2003/cowles-gamboa-van-baalen_matrix/support")
 (local
  (include-book "matrix" :dir :matrix)
  )
)

(encapsulate ()
  (add-include-book-dir :matrices "workshops/2003/hendrix/support")
 (local
  (include-book "matrices" :dir :matrices)
  )

 ;;tests from the paper
 (local
  (defthm col-count-m+
      (implies (matrixp m)
	       (equal (col-count (m+ m n))
		      (col-count m))))
  )
 )

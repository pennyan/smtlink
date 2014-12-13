;; This file proves basic linear algebra theorems
;; that are needed in the proof
;;
;; I need to revise this file into a executable version
;; and do unit test with my skip proofs
;;
;; Yan Peng
;; 2014/11/25
;;

(in-package "ACL2")

;;set current book directory to the acl2 book directory
:set-cbd "/ubc/cs/research/isd/users/software/ACL2/acl2-sources/books"

;; set up directories to book
;;   books/workshops/2003/cowles-gamboa-van-baalen_matrix/
(add-include-book-dir :matrix "workshops/2003/cowles-gamboa-van-baalen_matrix/support")
(include-book "matrix" :dir :matrix)

;; ------ basic linear algebra definitions ------ ;;

;; This is a recursive definition that says A is a
;; real matrix.
(defun m-elem-is-real (A)
  "Check if all elements of a matrix are reals."
  ;; I could use a guard here.
  (and (realp (cadar A))
       (m-elem-is-real (cdr A))))
(defun m-is-real (A)
  (and (alist2p 'A A)
       (m-elem-is-real A)))

(defun m-is-square (A)
  (and (alist2p 'A A)
       (equal (r A) (c A))))
(defun m-is-symmetric (A)
  (and (alist2p 'A A)
       (m-= A (m-trans A))))

(defun m-is-vector (v)
  (and (alist2p 'v v)
       (equal (c v) 1)))

;; This is another recursive definition that defines
;; a diagonal matrix.
(defun diag-elem (elem)
  (cond ((and (not (equal (caar elem) (cadar elem)))
	      (equal (cdar elem) 0)) t)
	((equal (caar elem) (cadar elem)) t)
	(t nil)))

(defun m-elem-is-diag (A)
  "Check if all elements of matrix A satisfies a diagonal matrix."
  (and (diag-elem (car A))
       (m-elem-is-diag (cdr A)))
  )

(defun m-is-diag (A)
  (and (alist2p 'A A)
       (m-elem-is-diag A)))
;; ------ basic linear algebra theorems ------- ;;

;; Below is a list of basic theorems


;; Below theorems are for the rewriting proofs
(defun m-=-transitivity-func (X Y Z)
  (implies (and (m-= X Y)
		(m-= Y Z))
	   (m-= X Z)))
(defthm m-=-transitivity
  (m-=-transitivity-func X Y Z)
  :rule-classes nil)

(defun left-s-*-distributive-func (k A B)
  (m-= (s-* k (m-- A B))
	(m-- (s-* k A) (s-* k B)))
  )
(skip-proofs
 (defthm left-s-*-distributive
   (left-s-*-distributive-func k A B)
   :rule-classes nil)
 )

(skip-proofs
 (defthm +-associative-4elem-1
   (m-= (m-- (m-- A B) (m-- C D))
	  (m-+ (m-- (m-- A B) C) D))
   :rule-classes nil))

(skip-proofs
 (defthm +-associative-4elem-2
   (m-= (m-+ (m-- (m-- A B) C) D)
	  (m-- (m-- A C) (m-- B D)))
   :rule-classes nil))

;; Ib-Ab = (I-A)b
(skip-proofs
 (defthm extract-common-vector
   (m-= (m-- b (m-* A b))
	(m-* (m-- (m-1 (r b)) A) b))
   :rule-classes nil)
)

;; s-* associative
(skip-proofs
 (defthm s-*-associative
   (m-= (s-* k (m-* A x))
	(m-* (s-* k A) x))
   :rule-classes nil)
 )

(defthm subtraction-congruence
  (implies (and (m-= x1 x2)
		(m-= y1 y2))
	   (m-= (m-- x1 y1) (m-- x2 y2)))
  :rule-classes nil)

;; distributitive for m-* over m--
(skip-proofs
(defthm m-*-distributive-over-m--
    (m-= (m-- (m-* X y) (m-* X z))
	 (m-* X (m-- y z)))
  :rule-classes nil)
)

;; ------------------ vector norm theorems --------------- ;;

(defun v-2norm (x)
  "This is a 2-norm of vector x"
  (m-* (m-trans x) x))

;; 2norm congruence
(skip-proofs
 (defthm 2norm-congruence
   (implies (m-= X Y)
	    (equal (v-2norm X) (v-2norm Y)))
   :rule-classes nil)
 )

;; ------------------ Matrix norm theorems ---------------- ;;

;; see topic quantifier tutorial
(defun-sk m-normp-forall (M M-Norm)
  (forall (x)
	  (implies (and (alist2p 'x x)
			(equal (c M) (r x))
			(equal (c x) 1)
			)
		   (<= (v-2norm (m-* M x))
		       (* M-Norm M-Norm (v-2norm x))))))

(defun-sk m-normp-exists (M M-Norm)
  (exists (x)
	  (and (alist2p 'x x)
	       (not (m-= x (m-0 (r x) (c x))))
	       (equal (c M) (r x))
	       (equal (c x) 1)
	       (equal (v-2norm (m-* M x))
		      (* M-Norm M-Norm (v-2norm x))))))

(defun m-normp (M M-Norm)
  ;;"This is definition of a matrix norm"
  (and (alist2p 'M M)
       (realp M-Norm)
       (m-normp-forall M M-Norm)
       (m-normp-exists M M-Norm))
  )

;; All matrix M has a matrix norm
(defun-sk matrix-has-m-norm (M)
  (exists (M-Norm)
	  (m-normp M M-Norm)))

(skip-proofs
 (defthm all-matrix-has-m-norm
     (matrix-has-m-norm M)
 :rule-classes nil))

;; Matrix norms are unique
(skip-proofs
 (defthm M-Norm-unique
   (implies (and (alist2p 'M M)
		 (realp norm1)
		 (realp norm2)
		 (m-normp M norm1)
		 (m-normp M norm2))
	    (equal norm1 norm2))
   :rule-classes nil)
 )


;; ------------------- preceq and pd ---------------------- ;;

;; (defun m-pd ())
;; (defun m-psd ())
;; (defun m-prec (A B) (m-pd (m-- A B)))
;; (defun m-preceq (A B) (m-psd (m-- A B)))













(in-theory (disable m-normp-exists m-normp-exists-suff m-normp-forall m-normp-forall-necc))

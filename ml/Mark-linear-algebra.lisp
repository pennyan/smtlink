(defun is-permutaion (list1 list2)
  (and (and (true-listp list1) (true-listp list2))
       (the elements of list1 are a permutation of the elements of list2)))

(defun m-is-real (A)
  (and (m-is-matrix A)
       (all of the elements of A are real)))

(defun m-is-square (A)
  (and (m-is-matrix A)
       (equals (m-nrows A) (m-ncols A))))

(defun m-is-symmetric (A)
  (and (m-is-matrix A)
       (equals A (m-transpose A))))

(defun m-is-vector (v)
  (and (m-is-matrix b)
       (equals (m-ncols b) 1)))

# If you want to be able to handle matrices with complex values,
# then you might want to define a m-conjugate-transpose operator
# and a m-conjugate-symmetric predicate.

(defun m-is-diag (A)
  (A is a diagonal matrix))

(defun m-diag (x)
  (cond ((x is a square matrix) (the vector of the diagonal elements of x))
	((x is a vector) (a diagonal matrix whose diagonal elements are x))
	nil))

(defun m-ident (dims)
  (cond ( (and (listp dims) (equals (length dims) 2))
	 (the (car dims) (car (cdr dims)) matrix with 1s on the main diagonal
	      and 0s everywhere else))
	( (naturalp dims) (m-ident (list dims dims)))
	( (m-is-vector dims) (m-ident (m-nrows dims)))
	( (m-is-matrix dims) (m-ident (m-rows dims) (m-cols dims)))))

(defun m-can-be-added (A B)
  (and (m-is-matrix A) (m-is-matrix B)
       (equal (m-nrows A) (m-nrows B))
       (equal (m-ncols A) (m-ncols B))))

(defun m-can-be-multiplied (A B)
  (and (m-is-matrix A) (m-is-matrix B)
       (equal (m-ncols A) (m-nrows B))))

# m-rs: return t iff A is real-symmetric
(defun m-rs (A)
  (and (m-is-real A)
       (m-is-symmetric A)))

# m-pd: return t iff A is positive definite
(defun m-pd (A)
  (and (m-is-square A)
       (forall x
	       (implies (and (m-is-vector x) (m-can-be-multiplied A x))
			(> (m-* (m-transpose x) A x) 0)))))

# m-psd: return t iff A is positive semi-definite
(defun m-psd (A) ...)


# m-rspd: return t iff A is real-symmetric, positive definite
(defun m-rspd (A)
  (and (m-rs A) (m-pd A)))

# m-rspsd: return t iff A is real-symmetric, positive semi-definite
(defun m-rspd (A)
  (and (m-rs A) (m-psd A)))


# partial ordering of matrices
(defun m-prec   (A B) (m-pd  (m-- A B)))
(defun m-preceq (A B) (m-psd (m-- A B)))

# (m-eig A) returns the eigenvalues of A
#   Maybe define using defchoose and the Jordan Canonical Form Theorem
(defun m-eig (A)
  (list the eigvenvalues of A))

# maybe I'll need to define some stuff about singular values

(defthm m-diag-eig (A)
  (implies (m-is-diagonal A)
	   (is-permutation (m-eig A) (m-diag A))))

(defthm m-rs-has-real-eigenvalues
    (implies (m-rs A)
	     (m-is-real (m-eig A)))
  # proof-hints or skip-proofs
    )

(defthm m-eigs-and-pd
    (implies (and (m-is-square A)
		  (m-is-real (m-eig A)))
	     (equals (> (min (m-eig A)) 0) (m-pd A))))

(defthm m-norm-is-max-sv
    (equals (m-norm A) (max (m-sv A)))
  # proof-hints or skip-proofs
    )

# If a matrix is real symmetric, then its singular values
# are the absolute values of its eigenvalues
(defthm m-rs-sv-equals-abs-of-eig
    (implies (m-rs A)
	     (is-permutation (m-sv A) (m-element-abs (m-eig A))))
  # proof-hints or skip-proofs
    )

(defthm m-rs-norm
    (implies (m-rs A)
	     (equals (m-norm A) (max (max (m-eig A)) (- (min m-eig A)))))
  # this follows easily from m-norm-is-max-sv and m-rs-sv-equals-abs-of-eig
    )

# the sum of two rs matrices is rs
(defthm m-rs-sum
    (implies (and (m-rs A) (m-rs B) (m-can-be-added A B))
	     (m-rs (m-+ A B)))
  # probably an actual proof for this one
    )

# the product of two rs matrices is rs
#   I don't use this theorem below, but I do use m-rs-sum.
#   If one of these theorems in included in the linear-algebra book,
#   then it will make sense to include both.
(defthm m-rs-prod
    (implies (and (m-rs A) (m-rs B) (m-can-be-added A B))
	     (m-rs (m-+ A B)))
  # probably an actual proof for this one
    )

# eig(A+b*I) = eig(A) + b.
# Note: I'm assuming that m-+, m-*, etc. are defined to handle
#  arguments that are scalars, and that these functions treat a vector
#  of length N as a N-by-1 matrix.
(defthm m-eig-shift
    (implies (is-scalar b)
	     (is-permutation (m-eig (m-plus A (m-* b (m-ident (m-size A)))))
			     (m-+ (m-eig A) b)))
  # proof-hints or skip-proofs
    )

# I believe that I now have the pieces to prove what Yan wanted
(defthm yans-theorem
    (implies (and (m-rspd A) (>= mu 0) (>= L 0) (>= alpha_k 0)
		  (m-preceq (m-* mu (m-ident A)) A)
		  (m-preceq A (m-* L (m-ident A))))
	     (<=  (m-norm (m-- (m-ident(A) (m-* alpha_k A))))
		  (max (abs (- 1 (* alpha_k mu)))
		       (abs (- 1 (* alpha_k L))))))
  # should be provable using the stuff above
    )

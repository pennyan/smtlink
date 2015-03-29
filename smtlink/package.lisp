(in-package "ACL2")

(defpkg "SL"
    (union-eq *common-lisp-symbols-from-main-lisp-package*
	      *acl2-exports*))

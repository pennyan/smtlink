;; test-SMT-formula is a file for testing SMT formula construction
(in-package "ACL2")
(include-book "SMT-formula")

;; const-list
(SMT-constant-list '((simpleconst 1)))

;; func-list
(SMT-function-list '((simplefun3 () 1)
		     (simplefun2 (x) (* x x))
		     (simplefun1 (x y) (- (* 2 (simplefun2 x) simpleconst) 
					  (* (simplefun3) x y)))))

;; decl-list
(SMT-declaration-list '((RATIONALP x)
 			(ACL2-NUMBERP y)))

;; hyp-list
(SMT-hypothesis-list '(and (and (not (<= x 0))) (> x y)))

;; concl-list
(SMT-conclusion-list '(> (simplefun x y) 0))

;; using SMT-formula
(SMT-formula  '((simpleconst 1))
	       '((simplefun3 () 1)
		 (simplefun2 (x) (* x x))
		 (simplefun1 (x y) (- (* 2 (simplefun2 x) simpleconst) 
				      (* (simplefun3) x y))))
	       '((RATIONALP x)
		 (ACL2-NUMBERP y))
	       '(and (and (not (<= x 0))) (> x y))
	       '(> (simplefun x y) 0))

;; calling SMT-formula-top
(SMT-formula-top :const-list
		 ((simpleconst 1))
		 :func-list
		 ((simplefun3 () 1)
		  (simplefun2 (x) (* x x))
		  (simplefun1 (x y) (- (* 2 (simplefun2 x) simpleconst) 
				       (* (simplefun3) x y))))
		 :decl-list
		 ((RATIONALP x)
		  (ACL2-NUMBERP y))
		 :hyp-list
		 (and (and (not (<= x 0))) (> x y))
		 :concl-list		 
		 (> (simplefun x y) 0))

;; test-SMT-formula is a file for testing SMT formula construction
(in-package "ACL2")
(include-book "../../SMT-formula")

;; const-list
(SMT-constant-list '((simpleconst 1)))

;; decl-list
(SMT-declaration-list '((RATIONALP x)
 			(INTEGERP y)))

;; hyp-list
(SMT-hypothesis-list '(and (and (not (<= x 0))) (> x y)))

;; concl-list
(SMT-conclusion-list '(<= (* x x) (* x y simpleconst)))

;; using SMT-formula
(SMT-formula  '((simpleconst 1))
	       '((RATIONALP x)
		 (INTEGERP y))
	       '(and (and (not (<= x 0))) (> x y))
	       '(<= (* x x) (* x y simpleconst)))

;; calling SMT-formula-top
(SMT-formula-top :const-list
		 ((simpleconst 1))
		 :decl-list
		 ((RATIONALP x)
		  (INTEGERP y))
		 :hyp-list
		 (and (and (not (<= x 0))) (> x y))
		 :concl-list		 
		 (<= (* x x) (* x y simpleconst)))

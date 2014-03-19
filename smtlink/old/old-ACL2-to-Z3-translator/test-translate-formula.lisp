;; test-SMT-formula is a file for testing SMT formula construction
(in-package "ACL2")
(include-book "../../translate-SMT-formula")

;; const-list
(SMT-constant-list '((simpleconst 1)))

;; decl-list
(SMT-declaration-list '((RATIONALP x)
 			(ACL2-NUMBERP y)))

;; hyp-list
(SMT-hypothesis-list '(and (and (not (<= x 0))) (> x y)))

;; concl-list
(SMT-conclusion-list '(> (simplefun x y) 0))

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

;; calling translator
(translate-SMT-formula (SMT-formula-top
			:const-list
			((simpleconst 1))
			:decl-list
			((RATIONALP x)
			 (INTEGERP y))
			:hyp-list
			(and (and (not (<= x 0))) (> x y))
			:concl-list		 
			(<= (* x x) (* x y simpleconst))))


;; 2014-07-01
;; add an expand level for function expansion
;; :hints
;;   (("Goal"
;;     :clause-processor
;;     (my-clause-processor clause
;; 			 '( (:expand (:functions ())
;;                                   (:expansion-level 1))
;; 			   (:python-file "test")
;; 			   (:let ())
;; 			   (:hypothesize ())
;; 			   (:use ((:type ())
;; 				  (:hypo ())
;; 				  (:main ()))))
;; 			 )))
;; 1. default: if no level provided, just onelevel
;; 2. if level provided, each function can be expanded
;; for that many levels

;; 2014-07-02
;; add recursive function replacement and type speficication
;; :hints
;;   (("Goal"
;;     :clause-processor
;;     (my-clause-processor clause
;; 			 '( (:expand (:functions ((fdco rationalp)
;;                                                (m integerp)))
;;                                   (:expansion-level 1))
;; 			   (:python-file "test")
;; 			   (:let ())
;; 			   (:hypothesize ())
;; 			   (:use ((:type ())
;; 				  (:hypo ())
;; 				  (:main ()))))
;; 			 )))

;; test cases
(in-package "ACL2")
;;(logic)
;;:set-state-ok t
;;:set-ignore-ok t

(include-book "arithmetic/top-with-meta" :dir :system)
(add-include-book-dir :cp "/ubc/cs/home/y/yanpeng/project/ACL2/smtlink")
(include-book "top" :dir :cp)
(tshell-ensure)

;; need the configurable trust tag
;;(defttag :Smtlink-custom-config)
;; configurations
(local
 (progn
   (defun my-smtlink-config ()
     (declare (xargs :guard t))
     (make-smtlink-config :dir-interface
			  "/ubc/cs/home/y/yanpeng/project/ACL2/smtlink/z3\_interface"
			  :dir-files
			  "z3\_files"
			  :SMT-module
			  "ACL22SMT"
			  :SMT-class
			  "to_smt"
			  :smt-cmd
			  "python"
			  :dir-expanded
			  "expanded"))
   (defattach smt-cnf my-smtlink-config)))

(defttag nil)
;; ;; test0
;; (defconst *a* 1)
;; (defun bar0 (x) (* 4 1/2 x))

;; ;; a very simple theorem
;; (defthm test0
;;   (implies (and (and (rationalp x)) (and))
;; 	   (equal (+ x x) (* *a* (bar0 x))))
;;   :hints
;;   (("Goal"
;;     :clause-processor
;;     (Smtlink clause
;; 	     '((:expand ((:functions ((bar0 rationalp)))
;;                    (:expansion-level 1)))
;; 	       )
;; 	     state))))

;; an example to test the expansion

(defun fac (n)
  (if (or (<= n 0) (not (integerp n)))
      1
    (* n (fac (1- n)))))

(defthm test-lemma (implies  (and
                             (IMPLIES
                              (IF
                               (INTEGERP N)
                               (IF (EQUAL |var4| (FAC (BINARY-+ '-1 |var3|)))
                                   (NOT (< '2 N))
                                   'NIL)
                               'NIL)
                              (INTEGERP |var4|))
                            
                             (IMPLIES
                              (IF (INTEGERP N) (NOT (< '2 N)) 'NIL)
                              (<
                               ((LAMBDA
                                 (|var0|)
                                 (IF
                                  (IF (NOT (< '0 |var0|))
                                      (NOT (< '0 |var0|))
                                      (NOT (INTEGERP |var0|)))
                                  '1
                                  (BINARY-*
                                   |var0|
                                   ((LAMBDA
                                     (|var1|)
                                     (IF
                                      (IF (NOT (< '0 |var1|))
                                          (NOT (< '0 |var1|))
                                          (NOT (INTEGERP |var1|)))
                                      '1
                                      (BINARY-*
                                       |var1|
                                       ((LAMBDA
                                         (|var2|)
                                         (IF
                                          (IF (NOT (< '0 |var2|))
                                              (NOT (< '0 |var2|))
                                              (NOT (INTEGERP |var2|)))
                                          '1
                                          (BINARY-*
                                           |var2|
                                           ((LAMBDA
                                             (|var3|)
                                             (IF
                                              (IF (NOT (< '0 |var3|))
                                                  (NOT (< '0 |var3|))
                                                  (NOT (INTEGERP |var3|)))
                                              '1
                                              (BINARY-*
                                               |var3|
                                               (FAC (BINARY-+ '-1 |var3|)))))
                                            (BINARY-+ '-1 |var2|)))))
                                        (BINARY-+ '-1 |var1|)))))
                                    (BINARY-+ '-1 |var0|)))))
                                N)
                               '10)))
                            (IMPLIES (IF (INTEGERP N) (NOT (< '2 N)) 'NIL)
                                     (< (FAC N) '10))))

(defthm fac-thm
  (implies (and (and (integerp n))
                (and (<= n 2)))
           (< (fac n) 10))
  :hints
  (("Goal"
    :clause-processor
    (Smtlink-custom-config clause
             '((:expand ((:functions ((fac integerp)))
                         (:expansion-level 4)))
               (:use ((:main (test-lemma)))))
             state)))
  )

;; ;; an example with counter example
;; (defthm test9
;;   (implies (and (and (rationalp a)
;;                      (rationalp b))
;;                 (and))
;;            (> (+ (* a a) (* b b)) (* 2 a b)))
;;   :hints
;;   (("Goal"
;;     :clause-processor
;;     (Smtlink clause
;;              '()
;;              state)
;;     )))

(local
 (progn
   (defun my-smtlink-expt-config ()
     (declare (xargs :guard t))
     (change-smtlink-config *default-smtlink-config*
			  :SMT-module
			  "RewriteExpt"
			  :SMT-class
			  "to_smt_w_expt"
        ))
   (defattach smt-cnf my-smtlink-expt-config)))

;; an example showing uninterpreted function usage
(defthm test8
  (implies (and (and (rationalp 2x!-++__)
                     (integerp n))
                (and (> 2x!-++__ 0)))
           (> (expt 2x!-++__ n) 0))
  :hints
  (("Goal"
    :clause-processor
    (Smtlink-custom-config clause
             '((:uninterpreted-functions ((expt rationalp integerp rationalp))))
             state)))
  )
;; ;; test1
;; (defun foo1 (x y) (* x (+ 1 y)))

;; ;; very first piece of test case
;; (defthm test1 (implies (and (and (rationalp x)
;; 				 (integerp y)
;; 				 (integerp z))
;; 			    (and (not (<= x 0))
;; 				 (equal z (- 7 3/2))
;; 				 (or (> x y) (> x (+ y 40/3)))))
;; 		       (< (foo1 x (foo1 x z)) (foo1 x y)))
;;   :hints
;;   (("Goal"
;;     :clause-processor
;;     (Smtlink clause
;; 	     '( (:expand ((:functions ((foo1 rationalp)))
;; 			  (:expansion-level 1)))
;; 	       (:python-file "test1")
;; 	       (:let ())
;; 	       (:hypothesize ())
;; 	       (:use ((:type ())
;; 		      (:hypo ())
;; 		      (:main ()))))
;; 	     state))))

;; ;; test2
;; (defun foo2 (x) (+ x 3))
;; (defun bar2 (y) (* 2 (foo2 y)))

;; (defthm test2
;;   (implies (and (and (rationalp y))
;; 		(and (> y 1)))
;; 	   (> (bar2 (foo2 y)) 12))
;;   :hints
;;   (("Goal"
;;     :clause-processor
;;     (Smtlink clause
;; 	     '( (:expand ((:functions ((foo2 rationalp)
;; 				       (bar2 rationalp)))
;; 			  (:expansion-level 1)))
;; 	       (:python-file "test2")
;; 	       (:let ())
;; 	       (:hypothesize ())
;; 	       (:use ((:type ())
;; 		      (:hypo ())
;; 		      (:main ()))))
;; 	     state))))

;; ;; test3
;; (defun foo3 (x args) (+ x (nth 0 args) (nth 1 args)))

;; (defthm test3
;;   (implies (and (and (rationalp x)
;; 		     (integerp i)
;; 		     (integerp j))
;; 		(and (> x 0)
;; 		     (> i 0)
;; 		     (> j 0)))
;; 	   (> (foo3 x '(i j)) 0))
;;   :hints
;;   (("Goal"
;;     :clause-processor
;;     (Smtlink clause
;; 	     '( (:expand ((:functions ((foo3 rationalp)))
;; 			  (:expansion-level 1))))
;; 	     state))))

;; ;; test4
;; ;; x^2 + y^2 >= 2xy
;; ;; a(x,y) = x*y
;; ;; b(x) = 2*x = (a 2 x)
;; ;; c(x,y) = x+y
;; ;; d(x) = x^2 = (a x x)
;; ;; e(x) = -x
;; ;; f(x,y) = x-y = (c x -y) = (c x (e y))
;; (defun a4 (x y) (* x y))
;; (defun b4 (x) (a4 2 x))
;; (defun c4 (x y) (+ x y))
;; (defun d4 (x) (a4 x x))
;; (defun e4 (x) (- x))
;; (defun f4 (x y) (c4 x (e4 y)))

;; (defthm test4
;;     (implies (and (and (rationalp a)
;; 		       (rationalp b))
;; 		  (and))
;; 	     (>= (f4 (d4 (c4 a b))
;; 		     (a4 (b4 a) b))
;; 		 (a4 (b4 a) b)))
;;   :hints
;;   (("Goal"
;;     :clause-processor
;;     (Smtlink clause
;; 	     '( (:expand ((:functions ((a4 rationalp)
;; 				       (b4 rationalp)
;; 				       (c4 rationalp)
;; 				       (d4 rationalp)
;; 				       (e4 rationalp)
;; 				       (f4 rationalp))))
;; 		 (:expansion-level 1)
;; 		 )
;; 	       (:python-file "test4")
;; 	       (:let ())
;; 	       (:hypothesize ())
;; 	       (:use ((:type ())
;; 		      (:hypo ())
;; 		      (:main ()))))
;; 	     state))))

;; ;; test5: with recursive call
;; ;; (fac)
;; ;; This test case is buggy!!!!!!!!!!!!!!!!!!!!!!
;; ;; Because isInteger is translated into isReal!!!!
;; ;; (defun fac (x) (if (zp x) 1 (* x (fac (1- x)))))

;; ;; (defthm test5
;; ;;     (implies (and (and (integerp a))
;; ;; 		  (and (>= a 10)))
;; ;; 	     (>= (fac a) 20))
;; ;;   :hints
;; ;;   (("Goal"
;; ;;     :clause-processor
;; ;;     (my-clause-processor clause
;; ;; 			 '( (:expand ((:functions ((fac integerp)
;; ;; 						   (zp booleanp)))
;; ;; 				      (:expansion-level 3)))
;; ;; 			    (:python-file "test5")
;; ;; 			    (:let ())
;; ;; 			    (:hypothesize ())
;; ;; 			    (:use ((:type ())
;; ;; 				   (:hypo ())
;; ;; 				   (:main ()))))
;; ;; 			 state))))


;; ;; test6: user given hypothesis
;; ;; a - real
;; ;; b - real
;; ;; gamma - real
;; ;; m - integer
;; ;; n - integer
;; ;; 0 < gamma < 1
;; ;; 0 < m < n
;; ;; adapted from test4: a^2 + b^2 >= 2ab

;; ;; 2*a*b*gamma^n <= -2*a*b*gamma^m + ...???
;; (defun a6 (x y) (* x y))
;; (defun b6 (x) (a6 2 x))
;; (defun c6 (x y) (+ x y))
;; (defun d6 (x) (a6 x x))
;; (defun e6 (x) (- x))
;; (defun f6 (x y) (c6 x (e6 y)))
;; (defun foo6 (x n) (expt x n))

;; (defthm test6
;;     (implies (and (and (rationalp a)
;; 		       (rationalp b)
;; 		       (rationalp gamma)
;; 		       (integerp m)
;; 		       (integerp n))
;; 		  (and (> gamma 0)
;; 		       (< gamma 1)
;; 		       (> m 0)
;; 		       (< m n)))
;; 	     (>= (a6 (expt gamma m)      ;;(* (expt gamma m) (- (* (+ a b) (+ a b)) (* 2 a b)))
;; 		    (f6 (d6 (c6 a b))
;; 			(a6 (b6 a) b)))
;; 		 (a6 (foo6 gamma n)      ;;(* (expt gamma n) (* 2 a b))
;; 		    (a6 (b6 a) b))))
;;   :hints
;;   (("Goal"
;;     :clause-processor
;;     (Smtlink clause
;; 	     '( (:expand ((:functions ((a6 rationalp)
;; 				       (b6 rationalp)
;; 				       (c6 rationalp)
;; 				       (d6 rationalp)
;; 				       (e6 rationalp)
;; 				       (f6 rationalp)
;; 				       (foo6 rationalp))))
;; 		 (:expansion-level 1))
;; 	       (:python-file "test6")
;; 	       (:let ((expt_gamma_m (expt gamma m) rationalp)
;; 		      (expt_gamma_n (expt gamma n) rationalp)))
;; 	       (:hypothesize ((< expt_gamma_n expt_gamma_m)
;; 			      (> expt_gamma_m 0)
;; 			      (> expt_gamma_n 0)))
;; 	       (:use ((:type ())
;; 		      (:hypo ())
;; 		      (:main ()))))
;; 	     state))))

;; ;; test7: user given hints
;; ;; Design:
;; ;; '( (:expand (...))
;; ;;    (:python-file "..")
;; ;;    (:let ((...)
;; ;;           (...)))
;; ;;    (:hypothesis ((...)
;; ;;                  (...)))
;; ;;    (:use (:type ((...) (...) (...)))
;; ;;          (:hypo ((...) (...) (...)))
;; ;;          (:main ((...) (...) (...)))))
;; ;; Explanation:
;; ;; The three classes of hints are seperately for types,
;; ;; hypotheses and the main theorem returned.
;; ;; Type theorems come from the type statements in let
;; ;; bindings, hypo theorems come from user provided hypotheses,
;; ;; and the main theorem is the implication from SMT result
;; ;; to the initial theorem we want to prove.
;; ;; Note:
;; ;; Each theorem can have multiple hints.
;; ;; 

;; (defthm hint-thm-7-1
;;   (implies (and (rationalp x)
;; 		(rationalp y))
;; 	   (>= (* (+ x y) (+ x y)) 0))
;;   :rule-classes :linear)

;; ;; (defthm hint-thm-7-2
;; ;;   (implies (and (rationalp x)
;; ;; 		(rationalp y))
;; ;; 	   (equal (* (+ x y) (+ x y))
;; ;; 		  (expt (+ x y) 2))))

;; (defthm test7
;;   (implies (and (and (rationalp x)
;; 		     (rationalp y))
;; 		(and))
;; 	   (>= (expt (+ x y) 2) 0))
;;   :hints
;;   (("Goal"
;;     :clause-processor
;;     (Smtlink clause
;; 	     '( (:expand ((:function ())
;; 			  (:expansion-level 1)))
;; 	       (:python-file "test7")
;; 	       (:let ((expt_plus_x_y_square (expt (+ x y) 2) rationalp)))
;; 	       (:hypothesize ((>= expt_plus_x_y_square 0)))
;; 	       (:use ((:type ())
;; 		      (:hypo ((hint-thm-7-1)))
;; 		      (:main (hint-thm-7-1))))
;; 	       )
;; 	     state))))

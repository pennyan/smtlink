;; test cases
(in-package "ACL2")
(include-book "./SMT-connect")

(logic)
:set-state-ok t

;; test0
(defconst *a* 1)
(defun bar0 (x) (* 2 x))

;; a very simple theorem
(defthm test0
  (implies (and (and (rationalp x)) (and))
	   (equal (+ x x) (* *a* (bar0 x))))
  :hints
  (("Goal"
    :clause-processor
    (my-clause-processor clause
			 '( (:expand (bar0))
			   (:python-file "test0")
			   (:let ())
			   (:hypothesize ()))
			 ))))

;; test1
(defun foo1 (x y) (* x (+ 1 y)))

;; very first piece of test case
(defthm test1 (implies (and (and (rationalp x)
				 (integerp y)
				 (integerp z))
			    (and (not (<= x 0))
				 (equal z (+ 3/2 4))
				 (or (> x y) (> x (+ y 40/3)))))
		       (> (foo1 x (foo1 x z)) (foo1 x y)))
  :hints
  (("Goal"
    :clause-processor
    (my-clause-processor clause
			 '( (:expand (foo1))
			   (:python-file "test1")
			   (:let ())
			   (:hypothesize ()))))))

;; test2
(defun foo2 (x) (+ x 3))
(defun bar2 (y) (* 2 (foo2 y)))

(defthm test2
  (implies (and (and (rationalp y))
		(and (> y 1)))
	   (> (bar2 (foo2 y)) 12))
  :hints
  (("Goal"
    :clause-processor
    (my-clause-processor clause
			 '( (:expand (foo2 bar2))
			    (:python-file "test2")
			    (:let ())
			    (:hypothesize ()))))))

;; test3
(defun foo3 (x args) (+ x (nth 0 args) (nth 1 args)))

(defthm test3
  (implies (and (and (rationalp x)
		     (integerp i)
		     (integerp j))
		(and (> x 0)
		     (> i 0)
		     (> j 0)))
	   (> (foo3 x '(i j)) 0))
  :hints
  (("Goal"
    :clause-processor
    (my-clause-processor clause
			 '( (:expand (foo3))
			    (:python-file "test3")
			    (:let ())
			    (:hypothesize ()))))))

;; test4
;; x^2 + y^2 >= 2xy
;; a(x,y) = x*y
;; b(x) = 2*x = (a 2 x)
;; c(x,y) = x+y
;; d(x) = x^2 = (a x x)
;; e(x) = -x
;; f(x,y) = x-y = (c x -y) = (c x (e y))
(defun a4 (x y) (* x y))
(defun b4 (x) (a4 2 x))
(defun c4 (x y) (+ x y))
(defun d4 (x) (a4 x x))
(defun e4 (x) (- x))
(defun f4 (x y) (c4 x (e4 y)))

(defthm test4
    (implies (and (and (rationalp a)
		       (rationalp b))
		  (and))
	     (>= (f4 (d4 (c4 a b))
		     (a4 (b4 a) b))
		 (a4 (b4 a) b)))
  :hints
  (("Goal"
    :clause-processor
    (my-clause-processor clause
			 '( (:expand (a4 b4 c4 d4 e4 f4))
			    (:python-file "test4")
			    (:let ())
			    (:hypothesize ()))))))

;; test5: with recursive call
;; (fac)
(defun fac (x) (if (zp x) 1 (* x (fac (1- x)))))

(defthm test5
    (implies (and (and (integerp a))
		  (and (>= a 10)))
	     (>= (fac a) 20))
  :hints
  (("Goal"
    :clause-processor
    (my-clause-processor clause
			 '( (:expand (fac))
			    (:python-file "test5")
			    (:let ())
			    (:hypothesize ()))))))

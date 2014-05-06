;; test cases
:logic

;; test0
(defconst *a* 1)
(defun bar1 (x) (* 2 x))

;; a very simple theorem
(defthm test0
  (implies (and (and (rationalp x)) (and))
	   (equal (+ x x) (* *a* (bar1 x))))
  :hints
            (("Goal"
              :clause-processor
              (my-clause-processor clause
				   '( (:expand (bar1) 1)
				      (:python-file "test0")
				      (:let ())
				      (:hypothesize ()))
				      ))))

;; test1
(defun foo1 (x y) (* x (+ 1 y)))

;; very first piece of test case
(thm (implies (and (and (rationalp x)
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
				   '( (:expand (foo1) 2)
				      (:python-file "test1")
				      (:let ())
				      (:hypothesize ()))))))

;; test2
(defun foo (x) (+ x 3))
(defun bar (y) (* 2 (foo y)))

(defthm test2
  (implies (and (and (rationalp y))
		(and (> y 1)))
	   (> (bar (foo y)) 12))
  :hints
  (("Goal"
    :clause-processor
    (my-clause-processor clause
			 '( (:expand (foo bar) 5)
			    (:python-file "test2")
			    (:let ())
			    (:hypothesize ()))))))

;; test3
(defun foo2 (x args) (+ x (nth 0 args) (nth 1 args)))

(defthm test4
  (implies (and (and (rationalp x)
		     (integerp i)
		     (integerp j))
		(and (> x 0)
		     (> i 0)
		     (> j 0)))
	   (> (foo2 x '(i j)) 0))
  :hints
  (("Goal"
    :clause-processor
    (my-clause-processor clause
			 '( (:expand (foo2) 1)
			    (:python-file "test3")
			    (:let ())
			    (:hypothesize ()))))))

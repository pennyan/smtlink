
(defthm contrived-let
  (implies (and (rationalp x) (< 0 x)
                (rationalp y) (< 0 y))
           (< 0 (let ((x (+ x y)) (y (- x y)))
                  (if (< x y) (* x y) (* x y)))))
  :hints(("Goal"
          :clause-processor
          (smtlink clause
                   '((:let ((c (* x y) rationalp)))
                     (:hypothesize ((< 0 c)))
                     (:python-file "contrived-let"))
                   state))))

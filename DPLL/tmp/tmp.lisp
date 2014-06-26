(implies
     (and (implies (and (integerp n-minus-3)
                        (<= 2 n-minus-3)
                        (<= 0 phi0)
                        (< phi0
                           (+ -1
                              (* 2
                                 (/ (+ 1
                                       (fix (* (+ 1 3200 1 (- n-minus-3) -3)
                                               1/3200)))))))
                        (< (+ (a (+ n-minus-3 2) phi0)
                              (* (/ (expt 5 n-minus-3))
                                 (b-sum 1 n-minus-3)))
                           0))
                   (< (+ (a (+ n-minus-3 3) phi0)
                         (* (/ (expt 5 (+ n-minus-3 1)))
                            (b-sum 1 (+ n-minus-3 1))))
                      0))
          (implies (and (integerp n-minus-3)
                        (equal n-minus-3 1)
                        (<= 0 phi0)
                        (< phi0
                           (+ -1
                              (* 2
                                 (/ (+ 1
                                       (fix (* (+ 1 3200 (- n-minus-3) -3)
                                               1/3200))))))))
                   (< (+ (a (+ n-minus-3 3) phi0)
                         (* (/ (expt 5 (+ n-minus-3 1)))
                            (b-sum 1 (+ n-minus-3 1))))
                      0))
          (not (or (not (integerp n-minus-3))
                   (< n-minus-3 1)))
          (implies (and (integerp (+ -1 n-minus-3))
                        (<= 1 (+ -1 n-minus-3))
                        (<= 0 phi0)
                        (< phi0
                           (+ -1
                              (* 2
                                 (/ (+ 1
                                       (fix (* (+ 1 3200 1 (- n-minus-3) -3)
                                               1/3200))))))))
                   (< (+ (a (+ -1 n-minus-3 3) phi0)
                         (* (/ (expt 5 (+ -1 n-minus-3 1)))
                            (b-sum 1 (+ -1 n-minus-3 1))))
                      0))
          (integerp n-minus-3)
          (<= 1 n-minus-3)
          (<= 0 phi0)
          (< phi0
             (+ -1
                (* 2
                   (/ (+ 1
                         (fix (* (+ 1 3200 (- n-minus-3) -3)
                                 1/3200))))))))
     (< (+ (a (+ n-minus-3 3) phi0)
           (* (/ (expt 5 (+ n-minus-3 1)))
              (b-sum 1 (+ n-minus-3 1))))
        0))

(implies
 (and
  (let
   ((expt_gamma_2n (/ (expt 5 (* 2 n))))
    (expt_gamma_2n_minus_1 (/ (expt 5 (+ -1 (* 2 n)))))
    (expt_gamma_2n_minus_2 (/ (expt 5 (+ -1 n -1 n))))
    (expt_gamma_2 1/25)
    (expt_gamma_1 1/5)
    (expt_gamma_2_minus_2n (/ (expt 5 (+ 2 (- (* 2 n)))))))
   (implies
       (and (and (rationalp expt_gamma_2_minus_2n)
                 (rationalp expt_gamma_1)
                 (rationalp expt_gamma_2)
                 (rationalp expt_gamma_2n_minus_2)
                 (rationalp expt_gamma_2n_minus_1)
                 (rationalp expt_gamma_2n)
                 (integerp n))
            (equal 1
                   (* expt_gamma_2n_minus_2
                      expt_gamma_2_minus_2n))
            (equal expt_gamma_2n_minus_1
                   (* expt_gamma_2n_minus_2 expt_gamma_1))
            (equal expt_gamma_2n
                   (* expt_gamma_2n_minus_2 expt_gamma_2))
            (<= 4 n))
       (equal (+ (* expt_gamma_2n
                    (+ (* 2
                          (/ (+ 1 (fix (* (+ -1 3200 (- n)) 1/3200)))))
                       (- (* 2
                             (/ (+ 1 (fix (* (+ 3200 (- n)) 1/3200))))))))
                 (* expt_gamma_2n_minus_1
                    (+ (* 2
                          (/ (+ 1 (fix (* (+ 3200 (- n)) 1/3200)))))
                       (- (* 2
                             (/ (+ 1
                                   (fix (* (+ 1 3200 (- n)) 1/3200))))))))
                 -1
                 (* 2
                    (/ (+ 1 (fix (+ (* 1/3200 (+ -1 n)) 1)))))
                 (* expt_gamma_2n_minus_2
                    (+ -1
                       (* 2
                          (/ (+ 1
                                (fix (+ (* 1/3200 (+ 1 (- n))) 1))))))))
              (* expt_gamma_2n_minus_2
                 (+ (* expt_gamma_2
                       (+ (* 2
                             (/ (+ 1 (fix (* (+ -1 3200 (- n)) 1/3200)))))
                          (- (* 2
                                (/ (+ 1 (fix (* (+ 3200 (- n)) 1/3200))))))))
                    (* expt_gamma_1
                       (+ (* 2
                             (/ (+ 1 (fix (* (+ 3200 (- n)) 1/3200)))))
                          (- (* 2
                                (/ (+ 1
                                      (fix (* (+ 1 3200 (- n)) 1/3200))))))))
                    (* expt_gamma_2_minus_2n
                       (+ -1
                          (* 2
                             (/ (+ 1 (fix (+ (* 1/3200 (+ -1 n)) 1)))))))
                    -1
                    (* 2
                       (/ (+ 1
                             (fix (+ (* 1/3200 (+ 1 (- n))) 1))))))))))
  (integerp n)
  (<= 4 n))
 (equal (+ (* (/ (expt 5 (* 2 n)))
              (+ (* 2
                    (/ (+ 1 (fix (* (+ -1 3200 (- n)) 1/3200)))))
                 (- (* 2
                       (/ (+ 1 (fix (* (+ 3200 (- n)) 1/3200))))))))
           (* (/ (expt 5 (+ -1 (* 2 n))))
              (+ (* 2
                    (/ (+ 1 (fix (* (+ 3200 (- n)) 1/3200)))))
                 (- (* 2
                       (/ (+ 1
                             (fix (* (+ 1 3200 (- n)) 1/3200))))))))
           -1
           (* 2
              (/ (+ 1 (fix (+ (* 1/3200 (+ -1 n)) 1)))))
           (* (/ (expt 5 (+ -1 n -1 n)))
              (+ -1
                 (* 2
                    (/ (+ 1
                          (fix (+ (* 1/3200 (+ 1 (- n))) 1))))))))
        (* (/ (expt 5 (+ -1 n -1 n)))
           (+ (* 1/25
                 (+ (* 2
                       (/ (+ 1 (fix (* (+ -1 3200 (- n)) 1/3200)))))
                    (- (* 2
                          (/ (+ 1 (fix (* (+ 3200 (- n)) 1/3200))))))))
              (* 1/5
                 (+ (* 2
                       (/ (+ 1 (fix (* (+ 3200 (- n)) 1/3200)))))
                    (- (* 2
                          (/ (+ 1
                                (fix (* (+ 1 3200 (- n)) 1/3200))))))))
              (* (/ (expt 5 (+ 2 (- (* 2 n)))))
                 (+ -1
                    (* 2
                       (/ (+ 1 (fix (+ (* 1/3200 (+ -1 n)) 1)))))))
              -1
              (* 2
                 (/ (+ 1
                       (fix (+ (* 1/3200 (+ 1 (- n))) 1)))))))))

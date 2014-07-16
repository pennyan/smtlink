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
              (integerp n)
              (rationalp g1)
              (rationalp v0))
         (equal (* expt_gamma_2_minus_2n
                   expt_gamma_2n_minus_2)
                1)
         (equal expt_gamma_2n_minus_1
                (* expt_gamma_2n_minus_2 expt_gamma_1))
         (equal expt_gamma_2n
                (* expt_gamma_2n_minus_2 expt_gamma_2))
         (<= 3 n)
         (equal g1 1/3200)
         (<= 9/10 v0)
         (<= v0 11/10))
    (equal
     (+ (* expt_gamma_2n
           (+ (* (fix (+ 1 (fix v0)))
                 (/ (+ 1
                       (fix (* (+ -1
                                  (* (+ (fix (+ 1 (fix v0))) -1) (/ g1))
                                  (- n))
                               g1)))))
              (- (* (fix (+ 1 (fix v0)))
                    (/ (+ 1
                          (fix (* (+ (* (+ (fix (+ 1 (fix v0))) -1) (/ g1))
                                     (- n))
                                  g1))))))))
        (* expt_gamma_2n_minus_1
           (+ (* (fix (+ 1 (fix v0)))
                 (/ (+ 1
                       (fix (* (+ (* (+ (fix (+ 1 (fix v0))) -1) (/ g1))
                                  (- n))
                               g1)))))
              (- (* (fix (+ 1 (fix v0)))
                    (/ (+ 1
                          (fix (* (+ 1 (* (+ (fix (+ 1 (fix v0))) -1) (/ g1))
                                     (- n))
                                  g1))))))))
        -1
        (* (fix (+ 1 (fix v0)))
           (/ (+ 1
                 (fix (+ (* g1 (+ -1 n))
                         (fix (+ 1 (fix v0)))
                         -1)))))
        (* expt_gamma_2n_minus_2
           (+ -1
              (* (fix (+ 1 (fix v0)))
                 (/ (+ 1
                       (fix (+ (* g1 (+ 1 (- n)))
                               (fix (+ 1 (fix v0)))
                               -1))))))))
     (*
      expt_gamma_2n_minus_2
      (+
        (* expt_gamma_2
           (+ (* (fix (+ 1 (fix v0)))
                 (/ (+ 1
                       (fix (* (+ -1
                                  (* (+ (fix (+ 1 (fix v0))) -1) (/ g1))
                                  (- n))
                               g1)))))
              (- (* (fix (+ 1 (fix v0)))
                    (/ (+ 1
                          (fix (* (+ (* (+ (fix (+ 1 (fix v0))) -1) (/ g1))
                                     (- n))
                                  g1))))))))
        (* expt_gamma_1
           (+ (* (fix (+ 1 (fix v0)))
                 (/ (+ 1
                       (fix (* (+ (* (+ (fix (+ 1 (fix v0))) -1) (/ g1))
                                  (- n))
                               g1)))))
              (- (* (fix (+ 1 (fix v0)))
                    (/ (+ 1
                          (fix (* (+ 1 (* (+ (fix (+ 1 (fix v0))) -1) (/ g1))
                                     (- n))
                                  g1))))))))
        (* expt_gamma_2_minus_2n
           (+ -1
              (* (fix (+ 1 (fix v0)))
                 (/ (+ 1
                       (fix (+ (* g1 (+ -1 n))
                               (fix (+ 1 (fix v0)))
                               -1)))))))
        -1
        (* (fix (+ 1 (fix v0)))
           (/ (+ 1
                 (fix (+ (* g1 (+ 1 (- n)))
                         (fix (+ 1 (fix v0)))
                         -1))))))))))
  (integerp n)
  (rationalp g1)
  (rationalp v0)
  (<= 3 n)
  (equal g1 1/3200)
  (<= 9/10 v0)
  (<= v0 11/10))
 (equal
  (+ (* (/ (expt 5 (* 2 n)))
        (+ (* (fix (+ 1 (fix v0)))
              (/ (+ 1
                    (fix (* (+ -1
                               (* (+ (fix (+ 1 (fix v0))) -1) (/ g1))
                               (- n))
                            g1)))))
           (- (* (fix (+ 1 (fix v0)))
                 (/ (+ 1
                       (fix (* (+ (* (+ (fix (+ 1 (fix v0))) -1) (/ g1))
                                  (- n))
                               g1))))))))
     (* (/ (expt 5 (+ -1 (* 2 n))))
        (+ (* (fix (+ 1 (fix v0)))
              (/ (+ 1
                    (fix (* (+ (* (+ (fix (+ 1 (fix v0))) -1) (/ g1))
                               (- n))
                            g1)))))
           (- (* (fix (+ 1 (fix v0)))
                 (/ (+ 1
                       (fix (* (+ 1 (* (+ (fix (+ 1 (fix v0))) -1) (/ g1))
                                  (- n))
                               g1))))))))
     -1
     (* (fix (+ 1 (fix v0)))
        (/ (+ 1
              (fix (+ (* g1 (+ -1 n))
                      (fix (+ 1 (fix v0)))
                      -1)))))
     (* (/ (expt 5 (+ -1 n -1 n)))
        (+ -1
           (* (fix (+ 1 (fix v0)))
              (/ (+ 1
                    (fix (+ (* g1 (+ 1 (- n)))
                            (fix (+ 1 (fix v0)))
                            -1))))))))
  (* (/ (expt 5 (+ -1 n -1 n)))
     (+ (* 1/25
           (+ (* (fix (+ 1 (fix v0)))
                 (/ (+ 1
                       (fix (* (+ -1
                                  (* (+ (fix (+ 1 (fix v0))) -1) (/ g1))
                                  (- n))
                               g1)))))
              (- (* (fix (+ 1 (fix v0)))
                    (/ (+ 1
                          (fix (* (+ (* (+ (fix (+ 1 (fix v0))) -1) (/ g1))
                                     (- n))
                                  g1))))))))
        (* 1/5
           (+ (* (fix (+ 1 (fix v0)))
                 (/ (+ 1
                       (fix (* (+ (* (+ (fix (+ 1 (fix v0))) -1) (/ g1))
                                  (- n))
                               g1)))))
              (- (* (fix (+ 1 (fix v0)))
                    (/ (+ 1
                          (fix (* (+ 1 (* (+ (fix (+ 1 (fix v0))) -1) (/ g1))
                                     (- n))
                                  g1))))))))
        (* (/ (expt 5 (+ 2 (- (* 2 n)))))
           (+ -1
              (* (fix (+ 1 (fix v0)))
                 (/ (+ 1
                       (fix (+ (* g1 (+ -1 n))
                               (fix (+ 1 (fix v0)))
                               -1)))))))
        -1
        (* (fix (+ 1 (fix v0)))
           (/ (+ 1
                 (fix (+ (* g1 (+ 1 (- n)))
                         (fix (+ 1 (fix v0)))
                         -1)))))))))

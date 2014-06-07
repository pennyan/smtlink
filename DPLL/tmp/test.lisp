(thm (and (or (not
                             ((lambda
                               (expt_gamma_h expt_gamma_minus_h h)
                               (implies
                                (if (if (rationalp expt_gamma_minus_h)
                                        (if (rationalp expt_gamma_h)
                                            (integerp h)
                                            'nil)
                                        'nil)
                                    (if (equal expt_gamma_minus_h
                                               (unary-/ expt_gamma_h))
                                        (if (< '1 expt_gamma_h)
                                            (not (< h '1))
                                            'nil)
                                        'nil)
                                    'nil)
                                (<
                                 (binary-+
                                  (binary-*
                                   expt_gamma_h
                                   ((lambda
                                     (|var0|)
                                     (binary-+
                                      '-1
                                      (binary-*
                                       (binary-* '1
                                                 (unary-/ (binary-* '1 '1)))
                                       (binary-*
                                        (binary-+ '1 (binary-* '1 '1))
                                        (unary-/
                                         (binary-+
                                          '1
                                          (binary-*
                                           '1
                                           (binary-+
                                            (binary-* |var0| '1/3200)
                                            (binary-+
                                             (binary-*
                                              (binary-*
                                               '1
                                               (unary-/
                                                (binary-* '1
                                                          (binary-* '1 '1))))
                                              (binary-+ '1 (binary-* '1 '1)))
                                             (unary--
                                                 (binary-*
                                                      '1
                                                      (unary-/ '1))))))))))))
                                    h))
                                  (binary-*
                                   expt_gamma_minus_h
                                   ((lambda
                                     (|var1|)
                                     (binary-+
                                      '-1
                                      (binary-*
                                       (binary-* '1
                                                 (unary-/ (binary-* '1 '1)))
                                       (binary-*
                                        (binary-+ '1 (binary-* '1 '1))
                                        (unary-/
                                         (binary-+
                                          '1
                                          (binary-*
                                           '1
                                           (binary-+
                                            (binary-* |var1| '1/3200)
                                            (binary-+
                                             (binary-*
                                              (binary-*
                                               '1
                                               (unary-/
                                                (binary-* '1
                                                          (binary-* '1 '1))))
                                              (binary-+ '1 (binary-* '1 '1)))
                                             (unary--
                                                 (binary-*
                                                      '1
                                                      (unary-/ '1))))))))))))
                                    (unary-- h))))
                                 '0)))
                              (b-term-expt h)
                              (b-term-expt (unary-- h))
                              h))
                            (implies
                             (if (integerp h) (not (< h '1)) 'nil)
                             (<
                              (binary-+ (binary-* (b-term-expt h)
                                                  (b-term-rest h))
                                        (binary-* (b-term-expt (unary-- h))
                                                  (b-term-rest (unary-- h))))
                              '0)))
                           (implies
                                (if (integerp h)
                                    (if (equal expt_gamma_h (b-term-expt h))
                                        (not (< h '1))
                                        'nil)
                                    'nil)
                                (rationalp expt_gamma_h))
                           (implies (if (integerp h)
                                        (if (equal expt_gamma_minus_h
                                                   (b-term-expt (unary-- h)))
                                            (not (< h '1))
                                            'nil)
                                        'nil)
                                    (rationalp expt_gamma_minus_h))))

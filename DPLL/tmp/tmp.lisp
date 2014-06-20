(implies (and (integerp n) (<= 4 n))
         (< (+ (* 25 n) (* 25 n))
            (denominator (* (/ (expt 5 n)) (/ (expt 5 n))))))

50n < 5^2n

2n < (1/5)^(2-2n)

50n < 25^n
1) n == 4, 200 < 25^4
2) n >= 5, suppose n = k-1, 50(k-1) < 25^(k-1), 50k = 50(k-1) + 50 < 25^(k-1) + 50 < 25*25^(k-1) = 25^k

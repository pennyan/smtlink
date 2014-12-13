;; This file contains test cases for basic linear algebra
;; theorems that I did skip-proofs to.
;; This ensures that my skip-proofs are not trivially false.
;;
;; If needed in the future, I'll turn these skip-proofs
;; into theorems.
;;
;; Yan Peng
;; 2014/12/12
;;

(in-package "ACL2")
(ld "basics.lisp")

;; m-=-transitivity
(let ((X '(((0 . 0) . 4)
	   ((0 . 1) . 3)
	   (:HEADER :DIMENSIONS (1 2)
	    :MAXIMUM-LENGTH 10
	    :DEFAULT 0
	    :NAME X)))
      (Y '(((0 . 0) . 1)
	   ((0 . 1) . 2)
	   (:HEADER :DIMENSIONS (1 2)
	    :MAXIMUM-LENGTH 10
	    :DEFAULT 0
	    :NAME Y)) )
      (Z '(((0 . 0) . 5)
	   ((0 . 1) . 10)
	   (:HEADER :DIMENSIONS (1 2)
	    :MAXIMUM-LENGTH 10
	    :DEFAULT 0
	    :NAME Z)) ))
  (fmx "m-=-transitivity is tested to be ~x0" (equal (m-=-transitivity-func X Y Z) t)))

;; left-s-*-distributive
(let ((k (/ 2 3))
      (A '(((0 . 0) . 4)
	   ((0 . 1) . 3)
	   (:HEADER :DIMENSIONS (1 2)
	    :MAXIMUM-LENGTH 10
	    :DEFAULT 0
	    :NAME X)))
      (B '(((0 . 0) . 1)
	   ((0 . 1) . 2)
	   (:HEADER :DIMENSIONS (1 2)
	    :MAXIMUM-LENGTH 10
	    :DEFAULT 0
	    :NAME Y)) ))
  (fmx "left-s-*-distributive is tested to be ~x0" (equal (left-s-*-distributive-func k A B) t)))

;; To be continued...

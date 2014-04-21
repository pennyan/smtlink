;; test cases
:logic

;; test0
(defun bar (x) (* 2 x))

;; a very simple theorem
(defthm test0
  (implies (and (and (rationalp x)) (and))
	   (equal (+ x x) (bar x)))
  :hints
            (("Goal"
              :clause-processor
              (my-clause-processor clause '((bar) 1 "test0")))))

;; test1
(defun foo (x y) (* x (+ 1 y)))

;; very first piece of test case
(thm (implies (and (and (rationalp x)
			(integerp y)
			(integerp z))
		   (and (not (<= x 0))
			(equal z (+ 2 4))
			(or (> x y) (> x (+ y 1)))))
	      (> (foo x (foo x z)) (foo x y)))
     :hints
            (("Goal"
              :clause-processor
              (my-clause-processor clause '((foo) 2 "test1")))))

;; Test cases:
;; 1. Without constant definition and function definitions:
;;   a. all types
;;   b. all operators
;;   c. exceptional cases
;; 2. With constant definitions
;; 3. With function definitions

;; test2
;; We are assuming specific format for the declarations and conditions, use "and" in the connections:
;; implies ( - (and decl1 decl2 decl3 ...)
;;           \
;;             (and cond1 cond2 cond3 ...))
;;         (concl)


ACL2 p!>(ld "test-all.lisp")

ACL2 Version 6.4.  Level 2.  Cbd 
"/ubc/cs/home/y/yanpeng/project/ACL2/smtlink/".
System books directory 
"/ubc/cs/research/isd/users/software/ACL2/acl2-sources/books/".
Type :help for help.
Type (good-bye) to quit completely out of ACL2.

ACL2 p!>>ACL2 !>>
Since bar is non-recursive, its admission is trivial.  We observe that
the type of bar is described by the theorem (acl2-numberp (bar x)).
We used primitive type reasoning.

Summary
Form:  ( defun bar ...)
Rules: ((:fake-rune-for-type-set nil))
Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
 bar
ACL2 !>>
ACL2 Warning [Subsume] in ( defthm test0 ...):  The previously added
rule commutativity-of-+ subsumes a newly proposed :rewrite rule generated
from test0, in the sense that the old rule rewrites a more general
target.  Because the new rule will be tried first, it may nonetheless
find application.

cl: ((implies (if (rationalp x) 't 'nil)
              (equal (binary-+ x x) (bar x))))
(bar)

 1

 "test0"

The final index number: 1
(implies (if (rationalp x) 't 'nil)
         (equal (binary-+ x x)
                ((lambda (|var0|) (binary-* '2 |var0|))
                 x)))

proved
; Z3: `python /ubc/cs/home/y/yanpeng/project/ACL2/smtlink/z3_files/test0.py`:
0.15 sec, 2,176 bytes
t
0
("proved")
Success!
 (((not (implies (if (rationalp x) 't 'nil)
                 (equal (binary-+ x x)
                        ((lambda (|var0|) (binary-* '2 |var0|))
                         x))))
   (implies (if (rationalp x) 't 'nil)
            (equal (binary-+ x x) (bar x)))))

Goal'

Q.E.D.

Summary
Form:  ( defthm test0 ...)
Rules: ((:definition bar)
        (:definition not)
        (:executable-counterpart tau-system))
Hint-events: ((:clause-processor my-clause-processor))
Warnings:  Subsume
Time:  0.01 seconds (prove: 0.00, print: 0.00, other: 0.00)
Prover steps counted:  53
 test0
ACL2 !>>
Since foo is non-recursive, its admission is trivial.  We observe that
the type of foo is described by the theorem (acl2-numberp (foo x y)).
We used primitive type reasoning.

Summary
Form:  ( defun foo ...)
Rules: ((:fake-rune-for-type-set nil))
Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
 foo
ACL2 !>>cl: ((implies (if (if (rationalp x)
                      (if (integerp y) (integerp z) 'nil)
                      'nil)
                  (if (not (not (< '0 x)))
                      (if (equal z (binary-+ '2 '4))
                          (if (< y x)
                              (< y x)
                              (< (binary-+ y '1) x))
                          'nil)
                      'nil)
                  'nil)
              (< (foo x y) (foo x (foo x z)))))
(foo)

 2

 "test1"

The final index number: 6
(implies (if (if (rationalp x)
                 (if (integerp y) (integerp z) 'nil)
                 'nil)
             (if (not (not (< '0 x)))
                 (if (equal z (binary-+ '2 '4))
                     (if (< y x)
                         (< y x)
                         (< (binary-+ y '1) x))
                     'nil)
                 'nil)
             'nil)
         (< ((lambda (|var0| |var1|)
                     (binary-* |var0| (binary-+ '1 |var1|)))
             x y)
            ((lambda (|var2| |var3|)
                     (binary-* |var2| (binary-+ '1 |var3|)))
             x
             ((lambda (|var4| |var5|)
                      (binary-* |var4| (binary-+ '1 |var5|)))
              x z))))

proved
; Z3: `python /ubc/cs/home/y/yanpeng/project/ACL2/smtlink/z3_files/test1.py`:
0.11 sec, 1,984 bytes
t
0
("proved")
Success!
 (((not (implies (if (if (rationalp x)
                         (if (integerp y) (integerp z) 'nil)
                         'nil)
                     (if (not (not (< '0 x)))
                         (if (equal z (binary-+ '2 '4))
                             (if (< y x)
                                 (< y x)
                                 (< (binary-+ y '1) x))
                             'nil)
                         'nil)
                     'nil)
                 (< ((lambda (|var0| |var1|)
                             (binary-* |var0| (binary-+ '1 |var1|)))
                     x y)
                    ((lambda (|var2| |var3|)
                             (binary-* |var2| (binary-+ '1 |var3|)))
                     x
                     ((lambda (|var4| |var5|)
                              (binary-* |var4| (binary-+ '1 |var5|)))
                      x z)))))
   (implies (if (if (rationalp x)
                    (if (integerp y) (integerp z) 'nil)
                    'nil)
                (if (not (not (< '0 x)))
                    (if (equal z (binary-+ '2 '4))
                        (if (< y x)
                            (< y x)
                            (< (binary-+ y '1) x))
                        'nil)
                    'nil)
                'nil)
            (< (foo x y) (foo x (foo x z))))))

Goal'
Goal''

Q.E.D.

Summary
Form:  ( THM ...)
Rules: ((:definition foo)
        (:definition not)
        (:executable-counterpart binary-+))
Hint-events: ((:clause-processor my-clause-processor))
Time:  0.01 seconds (prove: 0.01, print: 0.00, other: 0.00)
Prover steps counted:  199

Proof succeeded.
ACL2 !>>Bye.
 :eof
ACL2 !>

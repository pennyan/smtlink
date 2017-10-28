;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software


(in-package "SMT")
(include-book "../top")
(include-book "centaur/sv/tutorial/support" :dir :system)

(value-triple (tshell-ensure))
(add-default-hints '((SMT::SMT-process-hint clause)))

;; Section 2. A short tour
;; Example 1
(def-saved-event x^2-y^2
  (defun x^2-y^2 (x y) (- (* x x) (* y y))))

(def-saved-event poly-ineq
  (defthm poly-ineq-example
    (implies (and (real/rationalp x) (real/rationalp y)
                  (<= (+ (* (/ 9 8) x x) (* y y)) 1)
                  (<=  (x^2-y^2 x y) 1))
             (<= y (* 3 (- x (/ 17 8)) (- x (/ 17 8)))))
    :hints(("Goal"
            :smtlink nil)))
  )


(deftutorial Example-1
  :parents (Tutorial)
  :short "Example 1: the basics"
  :long "<h3>Example 1</h3>
<p>The first example is a basic polynomial inequality.  Let's say we want to
prove below theorem:</p>

<box>
<p>
<b><color rgb='#323cbe'>Theorem 1.</color></b>
@($\\forall x\\in R$) and @($\\forall y \\in R$), if @($ \\frac{9x^2}{8}+y^2 \\le 1$) and
@($ x^2+y^2 \\le 1$), then @($ y\\le3(x-\\frac{17}{8})^2$).
</p>
</box>

<p>Suppose we've defined a function called @('x^2-y^2') like below:</p>

@(`(:code ($ x^2-y^2))`)

<p>We define our theorem as:</p>

@(`(:code ($ poly-ineq))`)

<p>Smtlink should just prove this inequality without any problem.</p>
<p>Like is shown in the example, @(':smtlink') can be provided as a hint in the
standard @(see acl2::hints) in ACL2. In the most basic cases where Smtlink
handles everything, no @(see smt-hints) are required to be provided, Hence
@(':smtlink nil').</p>

<p>The output of this defthm should look similar to:</p>

@({
Goal'
SMT-goal-generator=>Expanding ... X^2-Y^2
Subgoal 4
Using default SMT-trusted-cp...
/tmp/py_file/smtlink.6Wt6m
; mktemp: `mkdir -p /tmp/py_file && mktemp /tmp/py_file/smtlink.XXXXX`: 0.01 sec, 8,544 bytes
proved
; SMT solver: `python /tmp/py_file/smtlink.6Wt6m`: 0.18 sec, 7,888 bytes
; rm -f: `rm -f /tmp/py_file/smtlink.6Wt6m`: 0.01 sec, 7,792 bytes
Proved!
Subgoal 3
Subgoal 3'
Subgoal 2
Subgoal 1

Summary
Form:  ( DEFTHM POLY-INEQ-EXAMPLE ...)
Rules: ((:DEFINITION HINT-PLEASE)
        (:DEFINITION NOT)
        (:DEFINITION X^2-Y^2)
        (:EXECUTABLE-COUNTERPART BINARY-*)
        (:EXECUTABLE-COUNTERPART UNARY--)
        (:EXECUTABLE-COUNTERPART UNARY-/)
        (:FAKE-RUNE-FOR-TYPE-SET NIL)
        (:REWRITE ASSOCIATIVITY-OF-+)
        (:REWRITE ACL2::COMMUTATIVITY-2-OF-+)
        (:REWRITE COMMUTATIVITY-OF-*)
        (:REWRITE COMMUTATIVITY-OF-+)
        (:REWRITE DISTRIBUTIVITY))
Hint-events: ((:CLAUSE-PROCESSOR PROCESS-HINT)
              (:CLAUSE-PROCESSOR SMT-TRUSTED-CP)
              (:CLAUSE-PROCESSOR SMTLINK-SUBGOALS))
Time:  0.25 seconds (prove: 0.25, print: 0.00, other: 0.00)
Prover steps counted:  633
POLY-INEQ-EXAMPLE
})

<p>Smtlink is a sequence of clause processors and computed hints. Calling
smtlink from the @(':hints') put the theorem term though a clause processor
looking for syntax errors in the @(see smt-hints). If nothing wrong, it will
generate a term to be recognized by the first computed-hint
@('SMT::SMT-process-hint'). The first computed-hint then installs the
next-to-be clause processor to work on the clause. The next is the main
verified clause processor. Function expansion happens here.</p>

<p>@('SMT-goal-generator=>Expanding ... X^2-Y^2') shows function expansion is
being conducted. </p>

<p>In this example, four subgoals are generated as a result of this clause
processor. The first subgoal is the goal to be sent to the trusted clause
processor that transliterates the term into the corresponding SMT form and
writes it out to a file. An SMT solver is called upon the file and results are
read back into ACL2.
</p>


")

(def-saved-event smtconf-expt-tutorial
  (defun my-smtlink-expt-config ()
    (declare (xargs :guard t))
    (change-smtlink-config *default-smtlink-config*
                           :interface-dir "../z3_interface"
                           :smt-module    "RewriteExpt"
                           :smt-class     "to_smt_w_expt"
                           :smt-cmd       "python"
                           :pythonpath    "")))

(def-saved-event smtconf-expt-defattach-tutorial
  (defattach custom-smt-cnf my-smtlink-expt-config))

;; Example 2
(def-saved-event ||x^2+y^2||^2
  (defun ||x^2+y^2||^2 (x y) (+ (* x x) (* y y))))

(def-saved-event poly-of-expt-example
  (encapsulate ()
    (local (include-book "arithmetic-5/top" :dir :system))
    (defthm poly-of-expt-example
      (implies (and (real/rationalp x) (real/rationalp y) (real/rationalp z)
                    (integerp m) (integerp n)
                    (< 0 z) (< z 1) (< 0 m) (< m n))
               (<= (* 2 (expt z n) x y)
                   (* (expt z m) (||x^2+y^2||^2 x y))))
      :hints (("Goal"
               :smtlink-custom (:functions ((expt :formals ((r rationalp)
                                                            (i rationalp))
                                                  :returns ((ex rationalp))
                                                  :level 0))
                                :hypotheses (((< (expt z n) (expt z m)))
                                             ((< 0 (expt z m)))
                                             ((< 0 (expt z n))))
                                :main-hint nil
                                :smt-fname ""
                                :int-to-rat t
                                :rm-file nil
                                :smt-solver-params nil))))))
(deftutorial Example-2
  :parents (Tutorial)
  :short "Example 2"
  :long "<h3>Example 2</h3>
         @(`(:code ($ smtconf-expt-tutorial))`)
         @(`(:code ($ smtconf-expt-defattach-tutorial))`)
         @(`(:code ($ ||x^2+y^2||^2))`)
         @(`(:code ($ poly-of-expt-example))`)")

;; Buggy example
(def-saved-event non-theorem-example
  (acl2::must-fail
   (defthm non-theorem
     (implies (and (real/rationalp x)
                   (real/rationalp y)
                   (integerp (/ x y)))
              (not (equal y 0)))
     :hints(("Goal"
             :smtlink nil))
     :rule-classes nil)))

(deftutorial Example-3
  :parents (Tutorial)
  :short "Example 3"
  :long "<h3>Example 3</h3>
         @(`(:code ($ non-theorem-example))`)")


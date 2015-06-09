(in-package "ACL2")

;; for the clause processor to work
(include-book "SMT-connect" :ttags :all)
(logic)
:set-state-ok t
:set-ignore-ok t
(tshell-ensure)

(local
 (progn
   (defun my-smtlink-config ()
     (declare (xargs :guard t))
     (make-smtlink-config
       :dir-interface "./z3_interface"
       :dir-files     "z3\_files"
       :SMT-module    "ACL22SMT"
       :SMT-class     "to_smt"
       :smt-cmd       "python"
       :dir-expanded  "expanded"))
   (defattach smt-cnf my-smtlink-config)))

; what happens if my formula doesn't have the prescribed structure?
(encapsulate ()
  (local (defthm rubbish
    (or (and (and (rationalp x) (rationalp y))
	     (< x y))
	(< x y))
    :hints(("Goal"
      :clause-processor
      (smtlink clause '((:python-file "rubbish")) state)))
    :rule-classes ((:rewrite :corollary
      (implies (and (rationalp x) (rationalp y)) (< x y))))))

  (defthm everything-is-true p
    :hints(("Goal"
      :in-theory (disable rubbish)
      :use((:instance rubbish (x 1) (y 0)))))
    :rule-classes nil))


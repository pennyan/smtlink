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
(defthm rubbish
  (implies (and (and (rationalp x) (< 0 x))
                (and (rationalp y) (< x y)))
      (< 0 y))
  :hints(("Goal"
    :clause-processor
    (smtlink clause '((:python-file "rubbish")) state)))
  :rule-classes nil)

;; This is a primary implementation to invoke Z3 and fetch the result

(in-package "ACL2")
(include-book "std/strings/top" :dir :system)
(include-book "centaur/misc/tshell" :dir :system)

(defun invoke-Z3 (z3-cmd filename)
  (let ((cmd (str::cat z3-cmd " " filename)))
    (time$ (tshell-call cmd
                        :print t
                        :save t)
           :msg "; Z3: `~s0`: ~st sec, ~sa bytes~%"
           :args (list cmd))))

(tshell-ensure)

(defun invoke-Z3-test (z3-cmd filename)
  (mv-let (finishedp exit-status lines)
          (invoke-Z3 z3-cmd filename)
          (mv finishedp exit-status lines)))

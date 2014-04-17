;; There are two files for the proof of recurrence model of the
;; DPLL: global.lisp, DPLL_functions.lisp and DPLL_theorems.lisp.
;; global.lisp
;; global.lisp defines global variables that are repeatedly
;; called in a lot of the functions.

(in-package "ACL2")
(defconst *g1* 1/3200)
(defconst *g2* (- (/ 1/3200 5)))
(defconst *ccode* 1)
(defconst *Kt* 4/5)
(defconst *N* 1)
(defconst *fref* 1)
(defconst *alpha* 1)
(defconst *beta* 1)
(defconst *f0* 1)
(defconst *v0* 1)

;; this is an equivalence check for RTL description
;; and the synthesized netlist implementation of 
;; a CDC crossing. 
;; CDC -- clock domain crossing
;; Yan Peng
;; 2014.06.14

(defun RTL (A B OLD CTRL)
  (or (and CTRL A B) 
      (and (not CTRL) OLD)))

(defun synNtlst (A B OLD CTRL)
  (or (and A B OLD)
      (and (not OLD) A B CTRL)
      (and OLD (not B) A (not CTRL))
      (and (not A) (not CTRL) OLD)))

(defthm equiv-RTL-synNtlst
    (implies (and (booleanp A)
		  (booleanp B)
		  (booleanp OLD)
		  (booleanp CTRL))
	     (equal (RTL A B OLD CTRL)
		    (synNtlst A B OLD CTRL))))

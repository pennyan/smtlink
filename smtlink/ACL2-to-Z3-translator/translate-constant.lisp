;; translate-constant-list constains functions for translating a SMT constant list in ACL2 into a Z3 line of code
;; The resulting translated formula is a nested list of symbols

(in-package "ACL2")
(include-book "translate-number")

;; translate-const-name 
(defun translate-const-name (const-name)
  "translate-const-name: translate a SMT constant name into Z3"
  const-name)


;; translate-constant
(defun translate-constant (const)
  "translate-constant: translate a SMT constant definition into Z3 code"
  (list (translate-const-name (car const)) '= (translate-number (cadr const))))

;; translate-constant-list
(defun translate-constant-list (const-list)
  "translate-constant-list: translate a SMT constant list in ACL2 into a Z3 line of code"
  (if (consp const-list)
      (cons (translate-constant (car const-list)) 
	    (cons #\Newline (translate-constant-list (cdr const-list))))
    nil))

;; SMT-run contains functions for 1. writing a translated formula into a python file
;;                                2. calling Z3 procedure from ACL2 on the python file and fetch the result
;;                                3. formatting the result into some format we need
(in-package "ACL2")
(include-book "std/strings/top" :dir :system)
(include-book "centaur/misc/tshell" :dir :system)
(include-book "std/io/top" :dir :system)

:set-state-ok t
(set-print-case :downcase state)

;; princ$-list-of-strings
(defun princ$-list-of-strings (alist channel state)
  "princ$-list-of-strings: the real function to print the Z3 program."
  (if (consp alist)
    (let ((state (princ$-list-of-strings (car alist) channel state)))
      (princ$-list-of-strings (cdr alist) channel state))
    (if (and (not (equal alist nil)) 
	     (not (acl2-numberp alist)))   ;; if alist is a number, should be treated seperately
      (princ$ (string alist) channel state)
      (if (acl2-numberp alist)
        (princ$ alist channel state)
        state))))

;; write-SMT-file
(defun write-SMT-file (filename translated-formula state)
  "write-SMT-file: writes the translated formula into a python file, it opens and closes the channel and write the including of Z3 inteface"
  (mv-let
   (channel state)
   (open-output-channel filename :character state)
   (let ((state (princ$-list-of-strings 
		 (coerce (append
			  (append 
			    (append (coerce "import sys" 'LIST)
				    (list #\Newline))
			    (append (coerce "sys.path.insert(0,\"../../z3\_interface\")" 'LIST)
				    (list #\Newline)))
			  (append (coerce "from ACL2\_translator import *" 'LIST)
				  (list #\Newline))) 
			  'STRING) 
			 channel state)))
     (let ((state (princ$-list-of-strings translated-formula channel state)))
       (close-output-channel channel state)))))

;; SMT-run
(defun SMT-run (z3-cmd filename)                                                   ;; should be configed
  "SMT-run: run the external SMT procedure from ACL2"
  (let ((cmd (str::cat z3-cmd " " filename)))
    (time$ (tshell-call cmd
                        :print t
                        :save t)
           :msg "; Z3: `~s0`: ~st sec, ~sa bytes~%"
           :args (list cmd))))



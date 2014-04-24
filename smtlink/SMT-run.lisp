;; SMT-run writes to Z3, invoke Z3 and gets the result
(in-package "ACL2")
(include-book "centaur/misc/tshell" :dir :system)
(include-book "std/io/top" :dir :system)
(include-book "config")

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

;; coerce a list of strings and characters into a string
(defun coerce-str-and-char-to-str (slist)
  "coerce-str-and-char-to-str: coerce a list of strings and characters into a string"
  (if (endp slist)
      nil
    (cond ((stringp (car slist))
	   (concatenate 'string
			(car slist)
			(coerce-str-and-char-to-str (cdr slist))))
	  ((characterp (car slist))
	   (concatenate 'string
			(coerce (list (car slist)) 'STRING)
			(coerce-str-and-char-to-str (cdr slist))))
	  (t (cw "Error(run): Invalid list ~q0." (car slist))))))

;; write-head
(defun write-head ()
  "write-head: writes the head of a z3 file"
  (coerce-str-and-char-to-str
   (list "from sys import path"
	 #\Newline
	 "path.insert(0,\"" *dir-interface* "\")"
	 #\Newline
	 "from " *z3-module* " import " *z3-class* ", Q"
	 #\Newline
	 "s = " *z3-class* "()"
	 #\Newline)))

;; write-SMT-file
(defun write-SMT-file (filename translated-formula state)
  "write-SMT-file: writes the translated formula into a python file, it opens and closes the channel and write the including of Z3 inteface"
  (mv-let
   (channel state)
   (open-output-channel! filename :character state)
   (let ((state (princ$-list-of-strings
		 (write-head) channel state)))
     (let ((state (princ$-list-of-strings translated-formula channel state)))
       (close-output-channel channel state)))))

;; write-expander-file
(defun write-expander-file (filename expanded-term state)
  "write-expander-file: write expanded term to a file"
  (mv-let
   (channel state)
   (open-output-channel! filename :character state)
   (let ((state
	  (princ$-list-of-strings
	   expanded-term channel state)))
     (close-output-channel channel state))))

;; SMT-run
(defun SMT-run (filename)                                     
  "SMT-run: run the external SMT procedure from ACL2"
  (let ((cmd (concatenate 'string *smt-cmd* " " filename)))
    (time$ (tshell-call cmd
                        :print t
                        :save t)
           :msg "; Z3: `~s0`: ~st sec, ~sa bytes~%"
           :args (list cmd))))


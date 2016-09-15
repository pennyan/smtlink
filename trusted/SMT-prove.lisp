;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software
;;

(in-package "SMT")
(include-book "../verified/SMT-hint-interface")
(include-book "../verified/SMT-config")

;; (defun mk-fname (directory fname-LISP suffix)
;;   (let ((dir (if (equal directory "") "/tmp/py_file" directory)))
;;     (cond ((equal fname-LISP "")
;;            (let ((cmd (concatenate 'string "mkdir -p " dir " && "
;;                                    "mktemp " dir "/smtlink" suffix ".XXXXX")))
;;              (mv-let (exit-status lines)
;;                (time$ (tshell-call cmd
;;                                    :print t
;;                                    :save t)
;;                       :msg "; mktemp: `~s0`: ~st sec, ~sa bytes~%"
;;                       :args (list cmd))
;;                (if (equal exit-status 0)
;;                    (car lines)
;;                  (er hard? 'top-level "Error: Generate file error.")))))
;;           ((stringp fname-LISP)
;;            (concatenate 'string dir "/" (string (lisp-to-python-names fname-LISP)) suffix))
;;           (t (er hard? 'top-level "Error: fname should either be a string or \"\"")))))

;; (defun write-SMT-file (py-term smt-file)
;;   (declare (ignore py-term smt-file))
;;   )

;; (defun SMT-prove (term)
;;   (b* ((fname (smtlink-hint->python-file (smt-hint)))
;;        (uninterpreted (smtlink-hint->uninterpreted (smt-hint)))
;;        (directory (smtlink-config->SMT-files-dir (smt-cnf)))
;;        (file-format (smtlink-config->file-format (smt-cnf)))
;;        (smt-file (mk-fname directory fname file-format))

;;        (translated-py-term (SMT-transliteration term))

;;        (state (write-SMT-file translated-py-term smt-file))

;;        (result (run-SMT-solver smt-file))))
;;   result)

(define SMT-prove (term)
  (or term t))

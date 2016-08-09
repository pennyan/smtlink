;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software
;;

;;
;; This book defines a computed hint that looks for the function
;; "SMT-please"

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)


(program)

(defun extract-hint-wrapper (cl)
  (cond ((endp cl) nil)
        (t (let ((lit (car cl)))
             (case-match lit
               ((('hint-please & ('quote kwd-alist)))
                kwd-alist)
               (& (extract-hint-wrapper (cdr cl))))))))

(defun SMT-hint-wrapper-hint (cl)
  (b* ((- (cw "cl entering hint-wrapper: ~q0" cl))
       (kwd-alist (extract-hint-wrapper cl)))
    (cond (kwd-alist
           (mv-let (pre post)
             (split-keyword-alist :expand kwd-alist)
             (cond
              (post ; then there was already an :expand hint; splice one in
               (assert$ (eq (car post) :expand)
                        `(:computed-hint-replacement
                          t
                          ,@pre
                          :expand ,(cons `(hint-please ',kwd-alist)
                                         (cadr post))
                          ,@post)))
              (t ; simply extend kwd-alist
               (prog2$ (cw "~q0" `(:computed-hint-replacement
                                   t
                                   :expand (hint-please ',kwd-alist)
                                   ,@kwd-alist))
                       `(:computed-hint-replacement
                         t
                         :expand (hint-please ',kwd-alist)
                         ,@kwd-alist))))))
          (t nil))))

(logic)

;; Add this line to your code to add a default hint of SMT-hint-wrapper-hint
;; (add-default-hints '((SMT-hint-wrapper-hint clause)))

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
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)


(defsection SMT-hint-wrapper
  :parents (Smtlink)
  :short "Define Smtlink hint wrapper"

(program)

(define extract-hint-wrapper (cl)
  (cond ((endp cl) (mv nil nil))
        (t (b* ((lit cl))
             (case-match lit
               ((('SMT-hint-please ('quote kwd-alist)) . term)
                (mv term kwd-alist))
               ((('ACL2-hint-please ('quote kwd-alist)) . term)
                (mv term kwd-alist))
               (& (extract-hint-wrapper (cdr cl))))))))

(define SMT-hint-wrapper-hint (cl)
  (b* ((- (cw "cl entering hint-wrapper: ~q0" cl))
       ((mv term kwd-alist) (extract-hint-wrapper cl))
       ;; (- (cw "term: ~q0" term))
       ;; (- (cw "kwd-alist: ~q0" kwd-alist))
       )
    (cond ((or term kwd-alist)
           (mv-let (pre post)
             (split-keyword-alist :in-theory kwd-alist)
             (cond
              (post ; then there was already an :expand hint; splice one in
               (assert$ (eq (car post) :in-theory)
                        `(:computed-hint-replacement
                          t
                          ,@pre
                          :in-theory (enable ACL2-hint-please ,@(cdadr post))
                          ,@(cddr post)
                          )))
              (t ; simply extend kwd-alist
               (prog2$ (cw "~q0" `(:computed-hint-replacement
                                   t
                                   :do-not '(preprocess)
                                   :in-theory (enable ACL2-hint-please)
                                   ,@kwd-alist
                                   ))
                       `(:computed-hint-replacement
                         t
                         :do-not '(preprocess)
                         :in-theory (enable ACL2-hint-please)
                         ,@kwd-alist
                         ))))))
          (t nil))))

(logic)

)
;; Add this line to your code to add a default hint of SMT-hint-wrapper-hint
;; (add-default-hints '((SMT-hint-wrapper-hint clause)))
;; Remove hint:
;; (remove-default-hints '((SMT-hint-wrapper-hint clause)))

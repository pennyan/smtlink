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
  (cond ((endp cl) (mv nil nil))
        (t (b* ((lit (car cl)))
             (case-match lit
               (('hint-please term ('quote kwd-alist))
                (mv term kwd-alist))
               (& (extract-hint-wrapper (cdr cl))))))))

(defun SMT-hint-wrapper-hint (cl)
  (b* ((- (cw "cl entering hint-wrapper: ~q0" cl))
       ((mv term kwd-alist) (extract-hint-wrapper cl))
       (- (cw "term: ~q0" term))
       (- (cw "kwd-alist: ~q0" kwd-alist)))
    (cond ((or term kwd-alist)
           (mv-let (pre post)
             (split-keyword-alist :in-theory kwd-alist)
             (cond
              (post ; then there was already an :expand hint; splice one in
               (assert$ (eq (car post) :in-theory)
                        `(:computed-hint-replacement
                          ('(,@pre ,@post))
                          :do-not '(preprocess)
                          :in-theory (enable hint-please ,@(cdadr post))
                          ;; :expand ,(cons `(hint-please ,term ',kwd-alist)
                          ;;                (cadr post))
                          )))
              (t ; simply extend kwd-alist
               (prog2$ (cw "~q0" `(:computed-hint-replacement
                                   ('(,@kwd-alist))
                                   :do-not '(preprocess)
                                   :in-theory (enable hint-please)
                                   ;; :expand (hint-please ,term ',kwd-alist)
                                   ))
                       `(:computed-hint-replacement
                         ('(,@kwd-alist))
                         :do-not '(preprocess)
                         :in-theory (enable hint-please)
                         ;; :expand (hint-please ,term ',kwd-alist)
                         ))))))
          (t nil))))

(logic)

;; Add this line to your code to add a default hint of SMT-hint-wrapper-hint
;; (add-default-hints '((SMT-hint-wrapper-hint clause)))
;; Remove hint:
;; (remove-default-hints '((SMT-hint-wrapper-hint clause)))

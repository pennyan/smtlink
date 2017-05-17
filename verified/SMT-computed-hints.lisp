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


(defsection SMT-computed-hints
  :parents (Smtlink)
  :short "Define Smtlink computed-hints"

  (defconst *SMT-computed-hints-table*
    '((process-hint . SMT-verified-cp-hint)
      (smt-hint . nil)
      (main-hint . nil)
      (A-hint . nil)))

  (program)

  (define extract-hint-wrapper (cl)
    (cond ((endp cl) (mv nil nil nil))
          (t (b* ((lit cl))
               (case-match lit
                 ((('hint-please ('quote kwd-alist) ('quote tag)) . term)
                  (mv term kwd-alist tag))
                 (& (extract-hint-wrapper (cdr cl))))))))

  (define SMT-verified-cp-hint (cl)
    (b* ((- (cw "cl entering SMT verified cp hint: ~q0" cl))
         ((mv term kwd-alist tag) (extract-hint-wrapper cl))
         (next-stage (cdr (assoc tag *SMT-computed-hints-table*))))
      (cond ((and (equal next-stage nil)
                  (or term kwd-alist))
             `(:computed-hint-replacement
               nil
               :do-not '(preprocess)
               ,@kwd-alist
               ))
            ((and next-stage
                  (or term kwd-alist))
             (mv-let (pre post)
               (split-keyword-alist :in-theory kwd-alist)
               (cond
                (post ; then there was already an :in-theory hint; splice one in
                 (assert$ (eq (car post) :in-theory)
                          `(:computed-hint-replacement
                            ((,next-stage clause))
                            ,@pre
                            :in-theory (enable hint-please ,@(cdadr post))
                            ,@(cddr post)
                            )))
                (t ; simply extend kwd-alist
                 (prog2$ (cw "~q0" `(:computed-hint-replacement
                                     ((,next-stage clause))
                                     :do-not '(preprocess)
                                     :in-theory (enable hint-please)
                                     ,@kwd-alist
                                     ))
                         `(:computed-hint-replacement
                           ((,next-stage clause))
                           :do-not '(preprocess)
                           :in-theory (enable hint-please)
                           ,@kwd-alist
                           ))))))
            (t nil))))

  (define SMT-process-hint (cl)
    (b* ((- (cw "cl entering process-hint: ~q0" cl))
         ((mv term kwd-alist tag) (extract-hint-wrapper cl))
         (next-stage (cdr (assoc tag *SMT-computed-hints-table*))))
      (cond ((and (equal next-stage nil)
                  (or term kwd-alist))
             `(:computed-hint-replacement
               nil
               :do-not '(preprocess)
               ,@kwd-alist
               ))
            ((and next-stage
                  (or term kwd-alist))
             (prog2$ (cw "~q0" `(:computed-hint-replacement
                                 ((,next-stage clause))
                                 :do-not '(preprocess)
                                 ,@kwd-alist
                                 ))
                     `(:computed-hint-replacement
                       ((,next-stage clause))
                       :do-not '(preprocess)
                       ,@kwd-alist
                       )))
            (t nil))))

  (logic)

  )
;; Add this line to your code to add a default hint of SMT-hint-wrapper-hint
;; (add-default-hints '((SMT-computed-hint clause)))
;; Remove hint:
;; (remove-default-hints '((SMT-computed-hint clause)))

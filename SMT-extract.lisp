;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (13th March, 2014)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software


;; SMT-extract extracts the declarations, hypotheses and conclusion from a SMT formula in ACL2.
;; A typical SMT formula is in below format:
;; (implies (and <decl-list>
;;               <hypo-list>)
;;          <concl-list>)

(in-package "ACL2")
(include-book "./helper")
(include-book "tools/bstar" :dir :system) 

;; get-orig-param
(defun get-orig-param (decl-list)
  "get-orig-param: given a declaration list of a SMT formula, return a list of variables appearing in the declaration list"
  (if (endp decl-list) nil
      (cons (cadar decl-list) (get-orig-param (cdr decl-list)))))

;; (mutual-recursion
;; ;; extract-decls-and-hypos-disjuncts
;; (defun extract-decls-and-hypos-disjuncts (expr)
;;   (cond ( (and (equal (len expr) 4)
;;                (equal (car expr) 'if)
;;                (equal (caddr expr) ''nil)) ; a disjunction
;;           (b*
;;            ( ( (mv decl-list1 hypo-list1) (extract-decls-and-hypos-disjuncts (cadr expr)) )
;;              ( (mv decl-list2 hypo-list2) (extract-decls-and-hypos-disjuncts (caddr expr)) ) )
;;            (mv (append decl-list1 decl-list2) (append hypo-list1 hypo-list2)) ) )
;;         ( (and (equal (len expr) 2)        ; a declaration
;;                (member (car expr) (list 'booleanp 'integerp 'rationalp)))
;;           (if (and (symbolp (cadr expr)) (cadr expr))
;;               (mv (list expr) nil)
;;             ( mv
;;               (er hard? 'top-level "Variable name ~q0 is not valid.~%" (cadr expr))
;;               nil)))
;;         ((equal (car expr) 'not)  ; a negated hypothesis or type declaration
;;          (extract-decls-and-hypos-neg-conjuncts (cadr expr)))
;;         ( t                                              ; another hypothesis
;;           (mv nil (list expr)))))

;; extract-decls-and-hypos-neg-conjuncts
(defun extract-decls-and-hypos-neg-conjuncts (expr)
  "extract declarations and other hypotheses from the antecedent of a clause"
  ; Notes:
  ;  1.  This code has worst-case complexity that is quadratic in the size of expr
  ;    because of the 'append' operations below.  We could make the complexity linear by writing
  ;    a helper function and passing the list of what we've seen so far along while traversing the
  ;    tree.  My guess is that expr will be relatively small; so, it's better to use
  ;    the simple, and "obviously correct" code.  Of course, if smtlink works *really* well, it
  ;    will eventually be used on *huge* problems, and we might want to use the more efficient
  ;    approach.  On the other hand, the SMT algorithms aren't exactly low-complexity.
  ;  2.  Hard-coding the list of reocgnized types is bad style.  I should figure out a way
  ;    to generalize this.  It probably makes sense to do that when we merge the association
  ;    lists for operators from SMT-formula.lisp and SMT-translate.lisp.
  (cond ( (and (equal (len expr) 4)
               (equal (car expr) 'if)
               (equal (cadddr expr) ''nil)) ; a conjunction
          (b*
           ( ( (mv decl-list1 hypo-list1) (extract-decls-and-hypos-neg-conjuncts (cadr expr)) )
             ( (mv decl-list2 hypo-list2) (extract-decls-and-hypos-neg-conjuncts (caddr expr)) ) )
           (mv (append decl-list1 decl-list2) (append hypo-list1 hypo-list2)) ) )
        ( (and (equal (len expr) 2)        ; a declaration
               (member (car expr) (list 'booleanp 'integerp 'rationalp)))
          (if (and (symbolp (cadr expr)) (cadr expr))
              (mv (list expr) nil)
            ( mv
              (er hard? 'top-level "Variable name ~q0 is not valid.~%" (cadr expr))
              nil)))
        ;; ((equal (car expr) 'not)  ; a negated hypothesis or type declaration
        ;;  (extract-decls-and-hypos-disjuncts (cadr expr)))
        ( t                                              ; another hypothesis
          (mv nil (list expr)))))
;;)

;; (defun validate-conclusion (concl)
;;   "Making sure the conclusion doesn't contain type predicates."
;;   )

;; (defun tree-head (tree)
;;   (if (and (not (equal (car tree) 'if))
;;            (not (equal (caadr) 'if))
;;            (not (equal () 'if)))
;;       (list )
;;     (list (if ()
;;               ()
;;             ())
;;           ()
;;           ()))

;; (defun tree-last (tree)
;;   ())

(defun SMT-extract-helper (expr)
  (cond ((and (equal (len expr) 3)
              (equal (car expr) 'implies))
         (mv (cadr expr) (caddr expr)))
        (t (mv (er hard? 'top-level "smtlink: badly formed clause -- should be (implies decl-and-hypo-tree concl)") nil))))

;; SMT-extract
(defun SMT-extract (term)
  "extract decl-list, hypo-list and concl from a ACL2 term"
  ;  term should be of the form (implies expr concl)
  ;    or of the form (h1 h2 h3 ... h_n-1 concl)
  ;    We first check to see that term has this form.
  ;    We then extract decl-list and hypo-list from expr.
 (prog2$ (cw "extract: ~q0~%" term)
  (b*
   ( ( (mv antecedant conclusion) (SMT-extract-helper term))
     ( (mv decl-list hypo-list) (extract-decls-and-hypos-neg-conjuncts antecedant))
     ( concl  conclusion))
   (mv decl-list hypo-list concl))))



;; (IF
;;           (NOT (RATIONALP V0))
;;           'T
;;           (IF
;;            (NOT (RATIONALP PHI0))
;;            'T
;;            (IF
;;             (NOT (RATIONALP DV))
;;             'T
;;             (IF
;;              (< (BINARY-* '10/9 V0) '1)
;;              'T
;;              (IF
;;               (< '11/10 V0)
;;               'T
;;               (IF
;;                (< '1 (UNARY-- (BINARY-* '8000 DV)))
;;                'T
;;                (IF
;;                 (< '1 (BINARY-* '8000 DV))
;;                 'T
;;                 (IF
;;                  (< PHI0 '0)
;;                  'T
;;                  (IF
;;                   (NOT
;;                    (<
;;                     PHI0
;;                     (BINARY-+
;;                      '-1
;;                      (BINARY-+
;;                       (UNARY-/ (BINARY-+ '2561/3200 V0))
;;                       (BINARY-+
;;                            (BINARY-* DV (UNARY-/ (BINARY-+ '2561/3200 V0)))
;;                            (BINARY-* V0
;;                                      (UNARY-/ (BINARY-+ '2561/3200 V0))))))))
;;                   'T
;;                   (<
;;                    (BINARY-+
;;                     (BINARY-* '1/3125 PHI0)
;;                     (BINARY-+
;;                      (UNARY-/ (BINARY-+ '3201/3200 V0))
;;                      (BINARY-+
;;                       (BINARY-* '1/125
;;                                 (UNARY-/ (BINARY-+ '1599/1600 V0)))
;;                       (BINARY-+
;;                        (BINARY-* '1/25
;;                                  (UNARY-/ (BINARY-+ '3199/3200 V0)))
;;                        (BINARY-+
;;                         (BINARY-* '1/625
;;                                   (UNARY-/ (BINARY-+ '3197/3200 V0)))
;;                         (BINARY-+
;;                          (BINARY-* DV (UNARY-/ (BINARY-+ '3201/3200 V0)))
;;                          (BINARY-+
;;                           (BINARY-* V0 (UNARY-/ (BINARY-+ '3201/3200 V0)))
;;                           (BINARY-+
;;                            (BINARY-*
;;                             '1/125
;;                             (BINARY-* DV (UNARY-/ (BINARY-+ '1599/1600 V0))))
;;                            (BINARY-+
;;                             (BINARY-*
;;                                  '1/125
;;                                  (BINARY-*
;;                                       V0 (UNARY-/ (BINARY-+ '1599/1600 V0))))
;;                             (BINARY-+
;;                              (BINARY-*
;;                                  '1/25
;;                                  (BINARY-*
;;                                       DV (UNARY-/ (BINARY-+ '3199/3200 V0))))
;;                              (BINARY-+
;;                               (BINARY-*
;;                                  '1/25
;;                                  (BINARY-*
;;                                       V0 (UNARY-/ (BINARY-+ '3199/3200 V0))))
;;                               (BINARY-+
;;                                (BINARY-*
;;                                  '1/625
;;                                  (BINARY-*
;;                                       DV (UNARY-/ (BINARY-+ '3197/3200 V0))))
;;                                (BINARY-*
;;                                 '1/625
;;                                 (BINARY-*
;;                                  V0
;;                                  (UNARY-/
;;                                       (BINARY-+ '3197/3200 V0))))))))))))))))
;;                    '656/625))))))))))

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


;; extract-decls-and-hypos
(defun extract-decls-and-hypos (decl-and-hypo-tree)
  "extract declarations and other hypotheses from the antecedent of a clause"
  ; Notes:
  ;  1.  This code has worst-case complexity that is quadratic in the size of decl-and-hypo-tree
  ;    because of the 'append' operations below.  We could make the complexity linear by writing
  ;    a helper function and passing the list of what we've seen so far along while traversing the
  ;    tree.  My guess is that decl-and-hypo-tree will be relatively small; so, it's better to use
  ;    the simple, and "obviously correct" code.  Of course, if smtlink works *really* well, it
  ;    will eventually be used on *huge* problems, and we might want to use the more efficient
  ;    approach.  On the other hand, the SMT algorithms aren't exactly low-complexity.
  ;  2.  Hard-coding the list of reocgnized types is bad style.  I should figure out a way
  ;    to generalize this.  It probably makes sense to do that when we merge the association
  ;    lists for operators from SMT-formula.lisp and SMT-translate.lisp.
  (cond ( (and (equal (len decl-and-hypo-tree) 4)
               (equal (car decl-and-hypo-tree) 'if)
               (equal (cadddr decl-and-hypo-tree) ''nil)) ; a conjunction
          (b*
	    ( ( (mv decl-list1 hypo-list1) (extract-decls-and-hypos (cadr decl-and-hypo-tree)) )
	      ( (mv decl-list2 hypo-list2) (extract-decls-and-hypos (caddr decl-and-hypo-tree)) ) )
	    (mv (append decl-list1 decl-list2) (append hypo-list1 hypo-list2)) ) )
        ( (and (equal (len decl-and-hypo-tree) 2)        ; a declaration
	       (member (car decl-and-hypo-tree) (list 'booleanp 'integerp 'rationalp)))
	  (mv (list decl-and-hypo-tree) nil) )
	( t                                              ; another hypothesis
	  (mv nil (list decl-and-hypo-tree)))))


;; SMT-extract
(defun SMT-extract-y (term)
  "extract decl-list, hypo-list and concl from a ACL2 term"
  ;  term should be of the form (implies decl-and-hypo-tree concl)
  ;    We first check to see that term has this form.
  ;    We then extract decl-list and hypo-list from decl-and-hypo-tree.
  (b*
    ( ( (when (or (not (equal (len term) 3)) (not (equal (car term) 'implies))))
        (mv (er hard? 'top-level
	        "smtlink: badly formed clause -- should be (implies decl-and-hypo-tree concl)")
	    nil nil) )
      ( (mv decl-list hypo-list) (extract-decls-and-hypos (cadr term)) )
      ( concl (caddr term) ) )
    (mv decl-list hypo-list concl)))

(defun SMT-extract (term)
  (b* ( ((mv decl-list hypo-list concl) (SMT-extract-y term))
        (- (cw "(mrg) SMT-extract:~%  term = ~x0~%  decl-list = ~x1~%  hypo-list = ~x2~%  concl = ~x3~%"
	        term decl-list hypo-list concl))
        (- (cw "  (and-list-logic hypo-list) = ~x0~%" (and-list-logic hypo-list))) )
      (mv decl-list hypo-list concl)))

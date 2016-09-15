;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software
;;

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "ordinals/lexicographic-ordering" :dir :system)
;; for lambda expression
(include-book "kestrel/utilities/terms" :dir :system)
;; for symbol-fix
(include-book "centaur/fty/basetypes" :dir :system)

;; Include SMT books
(include-book "SMT-hint-interface")


(defsection SMT-goal-generator
  :parents (Smtlink)
  :short "SMT-goal-generator generates the three type of goals for the verified
  clause processor"

  (defalist sym-nat-alist
    :key-type symbol
    :val-type natp
    :pred sym-nat-alistp
    :true-listp t)

  (defthm consp-of-sym-nat-alist-fix
    (implies (consp (sym-nat-alist-fix x)) (consp x))
    :hints (("Goal" :in-theory (enable sym-nat-alist-fix))))

  (defthm len-of-sym-nat-alist-fix-<
    (> (1+ (len x)) (len (sym-nat-alist-fix x)))
    :hints (("Goal" :in-theory (enable sym-nat-alist-fix))))

  (defthm natp-of-cdar-sym-nat-alist-fix
    (implies (consp (sym-nat-alist-fix x))
             (natp (cdar (sym-nat-alist-fix x))))
    :hints (("Goal" :in-theory (enable sym-nat-alist-fix))))

  (define update-fn-lvls ((fn symbolp) (fn-lvls sym-nat-alistp))
    :returns (updated-fn-lvls sym-nat-alistp)
    :measure (len fn-lvls)
    :hints (("Goal" :in-theory (enable sym-nat-alist-fix)))
    :enabled t
    (b* ((fn (mbe :logic (symbol-fix fn) :exec fn))
         (fn-lvls (mbe :logic (sym-nat-alist-fix fn-lvls) :exec fn-lvls))
         ((unless (consp fn-lvls)) nil)
         ((cons first rest) fn-lvls)
         ((cons this-fn this-lvl) first)
         ((unless (equal fn this-fn))
          (cons (cons this-fn this-lvl)
                (update-fn-lvls fn rest))))
      (if (zp this-lvl)
          (cons (cons this-fn 0) rest)
        (cons (cons this-fn (1- this-lvl)) rest)))
    ///
    (more-returns
     (updated-fn-lvls
      (implies (and (symbolp fn)
                    (sym-nat-alistp fn-lvls)
                    (consp fn-lvls)
                    (hons-get fn fn-lvls)
                    (not (equal (cdr (hons-get fn fn-lvls)) 0)))
               (< (cdr (assoc fn updated-fn-lvls))
                  (cdr (assoc fn fn-lvls))))
      :name updated-fn-lvls-decrease))
    )

  (define flatten-formals ((formal-lst decl-listp))
    :returns (formals symbol-listp)
    :measure (len formal-lst)
    :hints (("Goal" :in-theory (enable decl-list-fix)))
    :enabled t
    (b* ((formal-lst (mbe :logic (decl-list-fix formal-lst) :exec formal-lst))
         ((if (endp formal-lst)) nil)
         ((cons first rest) formal-lst)
         ((decl d) first))
      (cons d.name (flatten-formals rest))))

  (defprod ex-args
    ((term-lst pseudo-term-listp :default nil)
     (fn-lst func-alistp :default nil)
     (fn-lvls sym-nat-alistp :default nil)))

  (defthm natp-of-sum-lvls-lemma
    (implies (and (consp (sym-nat-alist-fix fn-lvls)) (natp x))
             (natp (+ (cdr (car (sym-nat-alist-fix fn-lvls))) x)))
    :hints (("Goal"
             :in-theory (enable sym-nat-alist-fix)
             :use ((:instance natp-of-cdar-sym-nat-alist-fix)))))

  (define sum-lvls ((fn-lvls sym-nat-alistp))
    :returns (sum natp :hints (("Goal"
                                :use ((:instance natp-of-sum-lvls-lemma
                                                 (x (sum-lvls (cdr (sym-nat-alist-fix fn-lvls)))))))))
    :measure (len fn-lvls)
    :hints (("Goal" :in-theory (enable sym-nat-alist-fix)))
    :enabled t
    (b* ((fn-lvls (mbe :logic (sym-nat-alist-fix fn-lvls) :exec fn-lvls))
         ((unless (consp fn-lvls)) 0)
         ((cons first rest) fn-lvls)
         ((cons & lvl) first))
      (+ lvl (sum-lvls rest)))
    ///
    (defthm sum-lvls-decrease-after-update
      (implies (and (symbolp fn)
                    (sym-nat-alistp fn-lvls)
                    (consp fn-lvls)
                    (hons-get fn fn-lvls)
                    (not (equal (cdr (hons-get fn fn-lvls)) 0)))
               (< (sum-lvls (update-fn-lvls fn fn-lvls))
                  (sum-lvls fn-lvls)))))

  (define expand-measure ((expand-args ex-args-p))
    :returns (m nat-listp)
    :enabled t
    (b* ((expand-args (mbe :logic (ex-args-fix expand-args) :exec expand-args))
         ((ex-args a) expand-args)
         (lvl-sum (sum-lvls a.fn-lvls)))
      (list lvl-sum (acl2-count a.term-lst))))

  (encapsulate ()
    (local (defthm lemma-1
             (implies (ex-args-p x)
                      (pseudo-term-listp (ex-args->term-lst x)))))

    (local (defthm lemma-2
             (implies (and (pseudo-term-listp y) (consp y))
                      (pseudo-termp (car y)))))

    (local (defthm lemma-3
             (implies (and (pseudo-termp z) (consp z) (not (equal (car z) 'quote)))
                      (pseudo-term-listp (cdr z)))))

    (defthm cdar-of-ex-args->term-lst-is-pseudo-term-list
      (implies (and (ex-args-p expand-args)
                    (consp (ex-args->term-lst expand-args))
                    (consp (car (ex-args->term-lst expand-args)))
                    (not (equal (caar (ex-args->term-lst expand-args)) 'quote)))
               (pseudo-term-listp (cdar (ex-args->term-lst expand-args)))))

    (local (defthm lemma-4
             (implies (and (pseudo-term-listp y) (consp y))
                      (pseudo-term-listp (cdr y)))))

    (defthm cdr-of-ex-args->term-lst-is-pseudo-term-list
      (implies (and (ex-args-p expand-args)
                    (consp (ex-args->term-lst expand-args)))
               (pseudo-term-listp (cdr (ex-args->term-lst expand-args)))))

    (local (defthm lemma-5
             (implies (and (pseudo-term-listp y) (consp y) (not (consp (car y))))
                      (symbolp (car y)))))

    (defthm symbolp-of-car-of-ex-args->term-lst
      (implies (and (ex-args-p expand-args)
                    (consp (ex-args->term-lst expand-args))
                    (not (consp (car (ex-args->term-lst expand-args)))))
               (symbolp (car (ex-args->term-lst expand-args)))))
    )

  (encapsulate ()
    (local (in-theory (enable pseudo-lambdap)))

    (defthm symbol-listp-of-formals-of-pseudo-lambdap
      (implies (pseudo-lambdap x) (symbol-listp (cadr x))))

    (defthm pseudo-termp-of-body-of-pseudo-lambdap
      (implies (pseudo-lambdap x) (pseudo-termp (caddr x))))

    (defthm consp-of-pseudo-lambdap
      (implies (pseudo-lambdap x) (consp x)))

    (defthm consp-of-cdr-of-pseudo-lambdap
      (implies (pseudo-lambdap x) (consp (cdr x))))

    (defthm consp-of-cddr-of-pseudo-lambdap
      (implies (pseudo-lambdap x) (consp (cddr x))))

    (defthm not-stringp-of-cadr-of-pseudo-lambdap
      (implies (pseudo-lambdap x) (not (stringp (cadr x)))))
    )

  (encapsulate ()
    (local (defthm natp-of-cdr-of-hons-get-of-ex-args->fn-lvls-of-ex-args-p
             (implies (and (ex-args-p x) (hons-assoc-equal foo (ex-args->fn-lvls x)))
                      (natp (cdr (hons-assoc-equal foo (ex-args->fn-lvls x)))))))

    (defthm integerp-of-cdr-of-hons-get-of-ex-args->fn-lvls-of-ex-args-p
      (implies (and (ex-args-p x) (hons-assoc-equal foo (ex-args->fn-lvls x)))
               (integerp (cdr (hons-assoc-equal foo (ex-args->fn-lvls x)))))
      :hints(("Goal" :use ((:instance natp-of-cdr-of-hons-get-of-ex-args->fn-lvls-of-ex-args-p (x x))))))

    (defthm non-neg-of-cdr-of-hons-get-of-ex-args->fn-lvls-of-ex-args-p
      (implies (and (ex-args-p x) (hons-assoc-equal foo (ex-args->fn-lvls x)))
               (<= 0 (cdr (hons-assoc-equal foo (ex-args->fn-lvls x)))))
      :hints(("Goal" :use ((:instance natp-of-cdr-of-hons-get-of-ex-args->fn-lvls-of-ex-args-p (x x)))))))

  (encapsulate
    ()
    (set-well-founded-relation l<)

    ;;
    ;; The hypotheses each function is going to generate:
    ;;
    ;; If it is a non-recursive function:
    ;;   Expanding for once should be enough.
    ;;   Then we don't need the return types theorems.
    ;;   Currently we are deciding that we don't need the more-returns theorems
    ;;     for non-recursive functions.
    ;;
    ;; If it is a recursive function, but not declared as uninterpreted:
    ;;   Detect it and report an error.
    ;;
    ;; If it is a uninterpreted function:
    ;;   Expand it to the lowest level.
    ;;   We need the return type theorem as auxiliary hypotheses.
    ;;   Instantiate more returns with lambdas and the function calls.
    ;;
    (define expand ((expand-args ex-args-p))
      :returns (expanded-terms pseudo-term-listp)
      :measure (expand-measure expand-args)
      :guard-debug t
      :hints
      (("Goal"
        :use ((:instance sum-lvls-decrease-after-update
                         (fn (car (car (ex-args->term-lst expand-args))))
                         (fn-lvls (ex-args->fn-lvls expand-args))))))
      :enabled t
      (b* (;; (expand-args (mbe :logic (ex-args-fix expand-args) :exec expand-args))
           ((unless (ex-args-p expand-args)) nil)
           ((ex-args a) expand-args)
           ((unless (consp a.term-lst)) nil)
           ((cons term rest) a.term-lst)
           ;; If first term is an atom, return the atom
           ;; then recurse on the rest of the list
           ((if (atom term))
            (cons term (expand (change-ex-args expand-args :term-lst rest))))
           ((if (and (equal (car term) 'quote)
                     (consp (cdr term))
                     (equal (cddr term) nil)))
            (cons term (expand (change-ex-args expand-args :term-lst rest))))
           ((unless (not (equal (car term) 'quote)))
            (er hard? 'SMT-goal-generator=>expand "messed up quote: ~q0" term))
           ;; The first term is now a function call:
           ;; Cons the function call and function actuals out of term
           ((cons fn-call fn-actuals) term)

           ;; See if the fn-call is a lambdap:
           (pseudo-lambda? (pseudo-lambdap fn-call))
           ;; If it is a pseudo-lambdap
           ((if pseudo-lambda?)
            (b* ((lambda-formals (lambda-formals fn-call))
                 (lambda-body (car (expand (change-ex-args expand-args :term-lst (list (lambda-body fn-call))))))
                 (lambda-actuals (expand (change-ex-args expand-args :term-lst fn-actuals)))
                 ((unless (equal (len lambda-formals) (len lambda-actuals)))
                  (er hard? 'SMT-goal-generator=>expand "You called your function with the wrong number of actuals: ~q0"
                      term)))
              (cons `((lambda ,lambda-formals ,lambda-body) ,@lambda-actuals)
                    (expand (change-ex-args expand-args :term-lst rest)))))

           ;; If fn-call is neither a lambda expression nor a function call
           ((unless (symbolp fn-call))
            (er hard? 'SMT-goal-generator=>expand "Unrecognizable term: ~q0" term))
           ;; Try finding function call from fn-lst
           (fn (hons-get fn-call a.fn-lst))
           ;; If fn-call doesn't exist in fn-lst, it can be a basic function,
           ;; in that case we don't do anything with it.
           ;; Otherwise it can be a function that's forgotten to be added to fn-lst.
           ;; The translator will fail to translate it and report an error.
           ((unless fn)
            (cons (cons fn-call (expand (change-ex-args expand-args :term-lst fn-actuals)))
                  (expand (change-ex-args expand-args :term-lst rest))))

           ;; Now fn is a function in fn-lst
           ;; If fn-call is already expanded to level 0, don't expand.
           (lvl-item (hons-get fn-call a.fn-lvls))
           ((unless lvl-item)
            (er hard? 'SMT-goal-generator=>expand "Function ~q0 exists in the definition list but not in the levels list?" fn-call))
           ((if (zp (cdr lvl-item)))
            (cons (cons fn-call (expand (change-ex-args expand-args :term-lst fn-actuals)))
                  (expand (change-ex-args expand-args :term-lst rest))))

           ;; If fn-call is not expanded to level 0, still can expand.
           (new-fn-lvls (update-fn-lvls fn-call a.fn-lvls))
           ((func f) (cdr fn))
           (formals (flatten-formals f.formals))
           (expanded-lambda-body
            (car (expand (change-ex-args expand-args :term-lst (list f.body) :fn-lvls new-fn-lvls))))
           (expanded-lambda `(lambda ,formals ,expanded-lambda-body))
           (expanded-term-list (expand (change-ex-args expand-args :term-lst fn-actuals)))
           ((unless (equal (len formals) (len expanded-term-list)))
            (er hard? 'SMT-goal-generator=>expand "You called your function with the wrong number of actuals: ~q0"
                term))
           )
        (cons `(,expanded-lambda ,@expanded-term-list)
              (expand (change-ex-args expand-args :term-lst rest))))
      )
    )

  (defthm pseudo-termp-of-car-of-expand
    (implies (ex-args-p expand-args)
             (pseudo-termp (car (expand expand-args)))))

  (define initialize-fn-lvls ((fn-lst func-alistp))
    :returns (fn-lvls sym-nat-alistp)
    :enabled t
    (b* (((unless (func-alistp fn-lst)) nil)
         ((unless (consp fn-lst)) nil)
         ((cons first rest) fn-lst)
         ((func f) (cdr first)))
      (cons (cons f.name f.expansion-depth) (initialize-fn-lvls rest))))

  ;; Generate auxiliary hypotheses from the user given hypotheses
  (define generate-hyp-hint-lst ((hyp-lst hint-pair-listp) (fn-lst func-alistp) (fn-lvls sym-nat-alistp))
    :returns (hyp-hint-lst hint-pair-listp)
    (b* (((if (endp hyp-lst)) nil)
         ((cons (hint-pair hyp) rest) hyp-lst)
         (G-prim (car (expand (make-ex-args :term-lst (list hyp.thm)
                                            :fn-lst fn-lst
                                            :fn-lvls fn-lvls)))))
      (cons (make-hint-pair :thm G-prim
                            :hints hyp.hints)
            (generate-hyp-hint-lst rest fn-lst fn-lvls))))

  ;; (define generate-fn-hint-pair ((hypo hint-pair-p)
  ;;                                (fn-name symbolp) (returns symbol-listp) (formals symbol-listp)
  ;;                                (actuals pseudo-term-listp))
  ;;   :returns (fn-hint-pair hint-pair-p)
  ;;   (b* (((hint-pair p) hypo)
  ;;        (free-vars (all-vars p.thm))
  ;;        ;; If the returns theorems contain free variables,
  ;;        ;; report an error.
  ;;        ((unless (subsetp free-vars (append returns formals)))
  ;;         (er hard? 'SMT-goal-generator=>generate-fn-hint-pair "Function returns theorem contain free variables: ~q0. The formals are: ~q1 and the returns are: ~q2." p.thm formals returns)))
  ;;     `((lambda ,formals ((lambda ,returns ,p.thm) (,fn-name ,@formals))) ,@actuals)))

  ;; (define generate-fn-returns-hint ((returns decl-listp) (fn-name symbolp)
  ;;                                   (formals decl-listp) (actuals pseudo-term-listp)
  ;;                                   (fn-hint-acc hint-pair-listp))
  ;;   :returns (fn-hint-lst hint-pair-listp :hyp :guard)
  ;;   :ignore-ok t
  ;;   nil)

  ;; (define generate-fn-more-returns-hint ((more-returns hint-pair-listp) (fn-name symbolp)
  ;;                                        (formals decl-listp) (actuals pseudo-term-listp)
  ;;                                        (fn-hint-acc hint-pair-listp))
  ;;   :returns (fn-hint-lst hint-pair-listp :hyp :guard)
  ;;   :ignore-ok t
  ;;   nil)

  ;; (define generate-fn-hint ((fn func-p) (fn-actuals pseudo-term-listp)
  ;;                           (fn-hint-acc hint-pair-listp))
  ;;   :returns (fn-hint-lst hint-pair-listp :hyp :guard)
  ;;   (b* (((func f) fn)
  ;;        ((unless f.uninterpreted)
  ;;         (er hard? 'SMT-goal-generator=>generate-fn-hint "Function call ~q0 still exists in term but it's not declared as an uninterpreted function." f.name))
  ;;        (new-fn-hint-acc
  ;;         (generate-fn-returns-hint f.returns f.name f.formals fn-actuals fn-hint-acc)))
  ;;     (generate-fn-more-returns-hint f.more-returns f.name f.formals fn-actuals new-fn-hint-acc)))


  ;; ;; function hypotheses generation arguments
  ;; (defprod fhg-args
  ;;   ((term-lst pseudo-term-listp :default nil)
  ;;    (fn-lst func-alistp :default nil)
  ;;    (fn-hint-acc hint-pair-listp :default nil)))

  ;; ;; Generate auxiliary hypotheses from function expansion
  ;; (define generate-fn-hint-lst ((args fhg-args-p))
  ;;   :returns (fn-hint-lst hint-pair-listp)
  ;;   (b* (;; If guard is violated, return nil
  ;;        ((unless (fhg-args-p args)) nil)
  ;;        ;; Bind the fields out of the defprod type
  ;;        ((fhg-args a) args)
  ;;        ;; If a.term-lst is nil,
  ;;        ;; return the function hint accumulator a.fn-hint-acc
  ;;        ((unless (consp a.term-lst)) a.fn-hint-acc)
  ;;        ;; If not,
  ;;        ;; cons the first element out of a.term-lst
  ;;        ((cons first rest) a.term-lst)

  ;;        ;; If first is symbolp, don't need to generate any hypo
  ;;        ((if (symbolp first))
  ;;         (generate-fn-hint-lst (change-fhg-args :term-lst rest)))
  ;;        ;; Else it must be a consp, if it is a quoted thingy
  ;;        ;; The quoted thingy (cadr term) can be a non-pseudo-termp.
  ;;        ((if (and (equal (car term) 'quote)
  ;;                  (consp (cdr term))
  ;;                  (equal (cddr term) nil)))
  ;;         (generate-fn-hint-lst (change-fhg-args :term-lst rest)))

  ;;        ;; Now first must be a true-listp
  ;;        ((cons fn-call fn-actuals) first)

  ;;        ;; If term is an atom, return fn-hint-acc
  ;;        ((if (atom G-prim)) fn-hint-acc)
  ;;        ;; If term is nil, return fn-hint-acc
  ;;        ((if (endp G-prim)) fn-hint-acc)
  ;;        ;; Cons the function call and function actuals out of term
  ;;        ((cons fn-call fn-actuals) term)
  ;;        ;; See if fn-call is a lambda expression
  ;;        (pseudo-lambda? (pseudo-lambdap fn-call))
  ;;        ;; Try finding function call from fn-lst
  ;;        (fn (hons-get fn-call fn-lst))
  ;;        ;; If fn-call does not belong to fn-lst and it is not a lambda,
  ;;        ;; then no need to add any hypotheses.
  ;;        ((unless (or fn pseudo-lambda?))
  ;;         (generate-fn-hint-lst-on-lst fn-actuals fn-lst fn-hint-acc))
  ;;        ;; If fn-call belongs to fn-lst
  ;;        ((if fn)
  ;;         (generate-fn-hint-lst-on-lst fn-actuals fn-lst
  ;;                                      (generate-fn-hint (cdr fn) fn-actuals fn-hint-acc)))
  ;;        ;; Else fn-call is a lambda expression
  ;;        (body-fn-hint-lst (generate-fn-hint-lst (lambda-body fn-call) fn-lst fn-hint-acc))
  ;;        )
  ;;     (generate-fn-hint-lst-on-lst fn-actuals fn-lst body-fn-hint-lst)))

  ;; Make fn-lst a fast alist
  (define make-alist-fn-lst ((fn-lst func-listp))
    :returns (fast-fn-lst func-alistp)
    :measure (len fn-lst)
    :enabled t
    (b* ((fn-lst (mbe :logic (func-list-fix fn-lst) :exec fn-lst))
         ((unless (consp fn-lst)) nil)
         ((cons first rest) fn-lst)
         ((func f) first))
      (cons (cons f.name f) (make-alist-fn-lst rest))))

  ;; The top level function for generating SMT goals: G-prim and A's
  (define SMT-goal-generator ((cl pseudo-term-listp) (hints smtlink-hint-p))
    :returns (new-hints smtlink-hint-p)
    :short "@(call SMT-goal-generator) is the top level function for generating SMT goals: G-prim and A's"

    (b* ((cl (mbe :logic (pseudo-term-list-fix cl) :exec cl))
         (hints (mbe :logic (smtlink-hint-fix hints) :exec hints))
         ((smtlink-hint h) hints)
         ;; Make a fast alist version of fn-lst
         (fn-lst (make-alist-fn-lst h.functions))
         (fn-lvls (initialize-fn-lvls fn-lst))

         ;; Generate user given hypotheses and their hints from hyp-lst
         (hyp-hint-lst (with-fast-alist fn-lst (generate-hyp-hint-lst h.hypotheses fn-lst fn-lvls)))

         ;; Expand main clause using fn-lst
         ;; Generate function hypotheses and their hints from fn-lst
         (G-prim
          (with-fast-alist fn-lst (car (expand (make-ex-args
                                                :term-lst (list (disjoin cl))
                                                :fn-lst fn-lst
                                                :fn-lvls fn-lvls)))))

         ;; Generate auxiliary hypotheses from function expansion
         (fn-hint-lst ;; (generate-fn-hint-lst G-prim fn-lst nil)
          nil)

         ;; Combine all auxiliary hypotheses
         (total-aux-hint-lst `(,@fn-hint-lst ,@hyp-hint-lst))

         ;; Combine expanded main clause and its hint
         (expanded-clause-w/-hint (make-hint-pair :thm G-prim :hints h.main-hint))

         ;; Update smtlink-hint
         (new-hints
          (change-smtlink-hint hints
                               :fast-functions fn-lst
                               :aux-hint-list total-aux-hint-lst
                               :expanded-clause-w/-hint expanded-clause-w/-hint
                               )))
      new-hints))
  )

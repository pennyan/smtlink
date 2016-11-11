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
;; for lambda expression
(include-book "kestrel/utilities/terms" :dir :system)
;; for symbol-fix
(include-book "centaur/fty/basetypes" :dir :system)
;; for symbol-list-fix
(include-book "centaur/fty/baselists" :dir :system)

;; Include SMT books
(include-book "SMT-hint-interface")
(include-book "SMT-extractor")
;; To be compatible with Arithmetic books
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

(defsection SMT-goal-generator
  :parents (Smtlink)
  :short "SMT-goal-generator generates the three type of goals for the verified clause processor"

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
                    (assoc-equal fn fn-lvls)
                    (not (equal (cdr (assoc-equal fn fn-lvls)) 0)))
               (< (cdr (assoc fn updated-fn-lvls))
                  (cdr (assoc fn fn-lvls))))
      :name updated-fn-lvls-decrease))
    )

  (defprod ex-args
    :parents (expand)
    :short "Argument list for function expand"
    ((term-lst pseudo-term-listp "List of terms to be expanded.
      The function finishes when all of them are expanded to given level." :default nil)
     (fn-lst func-alistp "List of function definitions to use for
      function expansion." :default nil)
     (fn-lvls sym-nat-alistp "Levels to expand each functions to." :default nil)
     (wrld-fn-len natp "Number of function definitions in curent world." :default 0)))

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
                    (assoc-equal fn fn-lvls)
                    (not (equal (cdr (assoc-equal fn fn-lvls)) 0)))
               (< (sum-lvls (update-fn-lvls fn fn-lvls))
                  (sum-lvls fn-lvls)))))

  (define expand-measure ((expand-args ex-args-p))
    :returns (m nat-listp)
    :enabled t
    (b* ((expand-args (mbe :logic (ex-args-fix expand-args) :exec expand-args))
         ((ex-args a) expand-args)
         (lvl-sum (sum-lvls a.fn-lvls)))
      (list a.wrld-fn-len lvl-sum (acl2-count a.term-lst))))

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

    (defthm pseudo-term-list-of-cdar-of-ex-args->term-lst
      (implies (and (ex-args-p expand-args)
                    (consp (ex-args->term-lst expand-args))
                    (consp (car (ex-args->term-lst expand-args)))
                    (not (equal (caar (ex-args->term-lst expand-args)) 'quote)))
               (pseudo-term-listp (cdar (ex-args->term-lst expand-args)))))

    (local (defthm lemma-4
             (implies (and (pseudo-term-listp y) (consp y))
                      (pseudo-term-listp (cdr y)))))

    (defthm pseudo-term-listp-of-cdr-of-ex-args->term-lst
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

    (defthm pseudo-termp-of-car-of-ex-args->term-lst
      (implies (and (ex-args-p expand-args)
                    (consp (ex-args->term-lst expand-args)))
               (pseudo-termp (car (ex-args->term-lst expand-args))))
      :hints (("Goal" :in-theory (enable pseudo-termp))))

    (defthm len-equal-of-formals-of-pseudo-lambdap-and-actuals-of-pseudo-termp
      (implies (and (ex-args-p expand-args)
                    (pseudo-termp (car (ex-args->term-lst expand-args)))
                    (pseudo-lambdap (car (car (ex-args->term-lst expand-args)))))
               (equal (len (cadr (car (car (ex-args->term-lst expand-args)))))
                      (len (cdr (car (ex-args->term-lst expand-args))))))
      :hints (("Goal" :in-theory (enable pseudo-termp pseudo-lambdap))))

    (local (defthm lemma-6
             (implies (and (pseudo-termp x) (not (symbolp x)) (not (pseudo-lambdap (car x))))
                      (symbolp (car x)))
             :hints (("Goal" :in-theory (enable pseudo-termp pseudo-lambdap)))))

    (defthm symbolp-of-caar-of-ex-args->term-lst
      (implies (and (ex-args-p expand-args)
                    (consp (ex-args->term-lst expand-args))
                    (not (symbolp (car (ex-args->term-lst expand-args))))
                    (not (pseudo-lambdap (car (car (ex-args->term-lst expand-args))))))
               (symbolp (car (car (ex-args->term-lst expand-args))))))

    (local (defthm lemma-7
             (implies (and (pseudo-termp x) (consp x) (equal (car x) 'quote))
                      (and (not (cddr x)) (consp (cdr x))))))

    (defthm not-cddr-of-car-of-pseudo-term-list-fix-of-expand-args->term-lst
      (implies (and (consp (ex-args->term-lst expand-args))
                    (consp (car (ex-args->term-lst expand-args)))
                    (not (symbolp (car (ex-args->term-lst expand-args))))
                    (equal (car (car (ex-args->term-lst expand-args))) 'quote))
               (not (cddr (car (ex-args->term-lst expand-args))))))

    (defthm consp-cdr-of-car-of-pseudo-term-list-fix-of-expand-args->term-lst
      (implies (and (consp (ex-args->term-lst expand-args))
                    (consp (car (ex-args->term-lst expand-args)))
                    (not (symbolp (car (ex-args->term-lst expand-args))))
                    (equal (car (car (ex-args->term-lst expand-args))) 'quote))
               (consp (cdr (car (ex-args->term-lst expand-args))))))

    (defthm pseudo-term-listp-of-pseudo-lambdap-of-cdar-ex-args->term-lst
      (implies (and (ex-args-p expand-args)
                    (consp (ex-args->term-lst expand-args))
                    (consp (car (ex-args->term-lst expand-args)))
                    (not (equal (caar (ex-args->term-lst expand-args)) 'quote)))
               (pseudo-term-listp (cdar (ex-args->term-lst expand-args)))))
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
    (local (defthm lemma-1
             (implies (ex-args-p x) (sym-nat-alistp (ex-args->fn-lvls x)))))

    (local (defthm lemma-2
             (implies (and (sym-nat-alistp y) (assoc-equal foo y))
                      (natp (cdr (assoc-equal foo y))))))

    (local (defthm lemma-3
             (implies (and (sym-nat-alistp y) (assoc-equal foo y))
                      (consp (assoc-equal foo y)))))

    (local (defthm natp-of-cdr-of-assoc-equal-of-ex-args->fn-lvls-of-ex-args-p
             (implies (and (ex-args-p x) (assoc-equal foo (ex-args->fn-lvls x)))
                      (natp (cdr (assoc-equal foo (ex-args->fn-lvls x)))))))

    (defthm integerp-of-cdr-of-assoc-equal-of-ex-args->fn-lvls-of-ex-args-p
      (implies (and (ex-args-p x) (assoc-equal foo (ex-args->fn-lvls x)))
               (integerp (cdr (assoc-equal foo (ex-args->fn-lvls x)))))
      :hints(("Goal" :use ((:instance natp-of-cdr-of-assoc-equal-of-ex-args->fn-lvls-of-ex-args-p (x x))))))

    (defthm non-neg-of-cdr-of-assoc-equal-of-ex-args->fn-lvls-of-ex-args-p
      (implies (and (ex-args-p x) (assoc-equal foo (ex-args->fn-lvls x)))
               (<= 0 (cdr (assoc-equal foo (ex-args->fn-lvls x)))))
      :hints(("Goal" :use ((:instance natp-of-cdr-of-assoc-equal-of-ex-args->fn-lvls-of-ex-args-p (x x))))))

    (defthm consp-of-assoc-equal-of-ex-args->fn-lvls-of-ex-args-p
      (implies (and (ex-args-p x) (assoc-equal foo (ex-args->fn-lvls x)))
               (consp (assoc-equal foo (ex-args->fn-lvls x)))))
    )

  ;; (defun filter-fn-symbs (lst wrld acc)
  ;;   (declare (xargs :guard (and (symbol-listp lst)
  ;;                               (plist-worldp wrld))))
  ;;   (cond ((endp lst) acc)
  ;;         (t (filter-fn-symbs (cdr lst)
  ;;                             wrld
  ;;                             (if (function-symbolp (car lst) wrld)
  ;;                                 (cons (car lst) acc)
  ;;                               acc)))))

  ;; ; The desired result:
  ;; (let* ((world (w state))
  ;;        (fns (remove-duplicates-eq
  ;;              (strip-cadrs (universal-theory :here)))))
  ;;   (filter-fn-symbs fns world nil))

  (defconst *SMT-basic-functions*
    `(binary-+ binary-* unary-/ unary--
               equal <
               implies if not
               lambda ))

  (encapsulate
    ()
    (set-well-founded-relation l<)

    ;; Q FOR YAN:
    ;; 1. merge expand-args->fn-lst and expand-args->fn-lvls
    ;; 2. change update-fn-lvls function so that old items are not deleted and update the measure function
    ;; 3. clean the code in a more structured way - treat lambdas in another function
    ;; 4. clean up the above encapsulated theorems, maybe in another file
    (define expand ((expand-args ex-args-p) state)
      :parents (SMT-goal-generator)
      :returns (expanded-terms pseudo-term-listp
                               :hints (("Goal" :use ((:instance not-cddr-of-car-of-pseudo-term-list-fix-of-expand-args->term-lst)
                                                     (:instance consp-cdr-of-car-of-pseudo-term-list-fix-of-expand-args->term-lst)))))
      :measure (expand-measure expand-args)
      :verify-guards nil
      :hints
      (("Goal"
        :use ((:instance sum-lvls-decrease-after-update
                         (fn (car (car (ex-args->term-lst expand-args))))
                         (fn-lvls (ex-args->fn-lvls expand-args))))))
      (b* ((expand-args (mbe :logic (ex-args-fix expand-args) :exec expand-args))
           ;; This binds expand-args to a, so that we can call a.term-lst ...
           ((ex-args a) expand-args)
           ((unless (consp a.term-lst)) nil)
           ((cons term rest) a.term-lst)
           ;; If first term is a symbolp, return the symbol
           ;; then recurse on the rest of the list
           ((if (symbolp term))
            (cons term (expand (change-ex-args a :term-lst rest) state)))
           ((if (equal (car term) 'quote))
            (cons term (expand (change-ex-args a :term-lst rest) state)))
           ;; The first term is now a function call:
           ;; Cons the function call and function actuals out of term
           ((cons fn-call fn-actuals) term)

           ;; If fn-call is a pseudo-lambdap
           ((if (pseudo-lambdap fn-call))
            (cons
             (b* ((lambda-formals (lambda-formals fn-call))
                  (lambda-body (car (expand (change-ex-args a :term-lst (list (lambda-body fn-call))) state)))
                  (lambda-actuals (expand (change-ex-args a :term-lst fn-actuals) state))
                  ((unless (mbt (equal (len lambda-formals) (len lambda-actuals)))) nil))
               `((lambda ,lambda-formals ,lambda-body) ,@lambda-actuals))
             (expand (change-ex-args a :term-lst rest) state)))

           ;; If fn-call is neither a lambda expression nor a function call
           ((unless (mbt (symbolp fn-call))) a.term-lst)
           ;; Try finding function call from fn-lst
           (fn (hons-get fn-call a.fn-lst))
           ;; If fn-call doesn't exist in fn-lst, it can be a basic function,
           ;; in that case we don't do anything with it.
           ;; Otherwise it can be a function that's forgotten to be added to fn-lst.
           ;; We are going to expand all function like this for one level.
           ;; If the function is basic or has already been expanded once.
           ((unless fn)
            (b* ((- (cw "here1"))
                 ((unless (function-symbolp fn-call (w state)))
                  (prog2$
                   (er hard? 'SMT-goal-generator=>expand "Should be a function call: ~q0" fn-call)
                   a.term-lst))
                 (- (cw "here2"))
                 (basic-function (member-equal fn-call *SMT-basic-functions*))
                 ((if (or basic-function (<= a.wrld-fn-len 0)))
                  (cons (cons fn-call (expand (change-ex-args a :term-lst fn-actuals) state))
                        (expand (change-ex-args a :term-lst rest) state)))
                 (- (cw "here3"))
                 (formals (formals fn-call (w state)))
                 ((unless (symbol-listp formals))
                  (prog2$
                   (er hard? 'SMT-goal-generator=>expand "Formals should be symbol-listp: ~q0" formals)
                   a.term-lst))
                 (- (cw "here4"))
                 (extract-res (meta-extract-formula fn-call state))
                 ((unless (true-listp extract-res))
                  (prog2$
                   (er hard? 'SMT-goal-generator=>expand "Function formula should be true-listp: ~q0" extract-res)
                   a.term-lst))
                 (- (cw "here5"))
                 (body (nth 2 extract-res))
                 ((unless (pseudo-termp body))
                  (prog2$
                   (er hard? 'SMT-goal-generator=>expand "Should be a pseudo-termp: ~q0" body)
                   a.term-lst))
                 (- (cw "Expanding ~q0 ...~%" fn-call))
                 (expanded-lambda-body
                  (car (expand (change-ex-args a
                                               :term-lst (list body)
                                               :fn-lvls (hons-acons fn-call 0 a.fn-lvls)
                                               :wrld-fn-len (1- a.wrld-fn-len))
                               state)))
                 (expanded-lambda `(lambda ,formals ,expanded-lambda-body))
                 (expanded-term-list (expand (change-ex-args a :term-lst fn-actuals) state))
                 ((unless (equal (len formals) (len expanded-term-list)))
                  (prog2$
                   (er hard? 'SMT-goal-generator=>expand "You called your function with the wrong number of actuals: ~q0" term) a.term-lst)))
              (cons `(,expanded-lambda ,@expanded-term-list)
                    (expand (change-ex-args a :term-lst rest) state))))

           ;; Now fn is a function in fn-lst
           ;; If fn-call is already expanded to level 0, don't expand.
           (lvl-item (assoc-equal fn-call a.fn-lvls))
           ((unless lvl-item)
            (prog2$
             (er hard? 'SMT-goal-generator=>expand "Function ~q0 exists in the definition list but not in the levels list?" fn-call)
             a.term-lst))
           ((if (zp (cdr lvl-item)))
            (cons (cons fn-call (expand (change-ex-args a :term-lst fn-actuals) state))
                  (expand (change-ex-args a :term-lst rest) state)))

           ;; If fn-call is not expanded to level 0, still can expand.
           (new-fn-lvls (update-fn-lvls fn-call a.fn-lvls))
           ((func f) (cdr fn))
           (formals f.flattened-formals)
           (expanded-lambda-body
            (car (expand (change-ex-args a :term-lst (list f.body) :fn-lvls new-fn-lvls) state)))
           (expanded-lambda `(lambda ,formals ,expanded-lambda-body))
           (expanded-term-list (expand (change-ex-args a :term-lst fn-actuals) state))
           ((unless (equal (len formals) (len expanded-term-list)))
            (prog2$
             (er hard? 'SMT-goal-generator=>expand "You called your function with the wrong number of actuals: ~q0"
                 term)
             a.term-lst))
           )
        (cons `(,expanded-lambda ,@expanded-term-list)
              (expand (change-ex-args a :term-lst rest) state)))
      ///
      (more-returns
       (expanded-terms (implies (ex-args-p expand-args)
                                (pseudo-termp (car expanded-terms)))
                       :name pseudo-termp-of-car-of-expand
                       :hints (("Goal" :use ((:instance pseudo-term-listp-of-expand)))))
       (expanded-terms (implies (ex-args-p expand-args)
                                (equal (len expanded-terms)
                                       (len (ex-args->term-lst expand-args))))
                       :name len-of-expand))
      )
    )

  (verify-guards expand
    :hints (("Goal" :use ((:instance pseudo-term-listp-of-pseudo-lambdap-of-cdar-ex-args->term-lst)))))

  (define initialize-fn-lvls ((fn-lst func-alistp))
    :returns (fn-lvls sym-nat-alistp)
    :measure (len fn-lst)
    :hints (("Goal" :in-theory (enable func-alist-fix)))
    :enabled t
    (b* ((fn-lst (mbe :logic (func-alist-fix fn-lst) :exec fn-lst))
         ((unless (consp fn-lst)) nil)
         ((cons first rest) fn-lst)
         ((func f) (cdr first)))
      (cons (cons f.name f.expansion-depth) (initialize-fn-lvls rest))))

  ;; Generate auxiliary hypotheses from the user given hypotheses
  (define generate-hyp-hint-lst ((hyp-lst hint-pair-listp)
                                 (fn-lst func-alistp) (fn-lvls sym-nat-alistp)
                                 state)
    :returns (hyp-hint-lst hint-pair-listp)
    :enabled t
    (b* (((if (endp hyp-lst)) nil)
         ((cons (hint-pair hyp) rest) hyp-lst)
         (G-prim (car (expand (make-ex-args :term-lst (list hyp.thm)
                                            :fn-lst fn-lst
                                            :fn-lvls fn-lvls) state))))
      (cons (make-hint-pair :thm G-prim
                            :hints hyp.hints)
            (generate-hyp-hint-lst rest fn-lst fn-lvls state))))

  (define lambda->actuals-fix ((formals symbol-listp) (actuals pseudo-term-listp))
    :returns (new-actuals pseudo-term-listp)
    :enabled t
    (b* ((formals (mbe :logic (symbol-list-fix formals) :exec formals))
         (actuals (mbe :logic (pseudo-term-list-fix actuals) :exec actuals))
         (len-formals (len formals))
         (len-actuals (len actuals))
         ((if (equal len-formals len-actuals)) actuals))
      nil))

  (define lambda->formals-fix ((formals symbol-listp) (actuals pseudo-term-listp))
    :returns (new-formals symbol-listp)
    :enabled t
    (b* ((formals (mbe :logic (symbol-list-fix formals) :exec formals))
         (actuals (mbe :logic (pseudo-term-list-fix actuals) :exec actuals))
         (len-formals (len formals))
         (len-actuals (len actuals))
         ((if (equal len-formals len-actuals)) formals))
      nil))

  (defprod lambda-binding
    ((formals symbol-listp
              :default nil
              :reqfix (lambda->formals-fix formals actuals))
     (actuals pseudo-term-listp
              :default nil
              :reqfix (lambda->actuals-fix formals actuals)))
    :require (equal (len formals) (len actuals)))

  (deflist lambda-binding-list
    :elt-type lambda-binding
    :pred lambda-binding-listp
    :true-listp t)

  (define generate-lambda-bindings ((lambda-bd-lst lambda-binding-listp) (term pseudo-termp))
    :returns (new-term pseudo-termp)
    :measure (len lambda-bd-lst)
    :enabled t
    (b* ((lambda-bd-lst (mbe :logic (lambda-binding-list-fix lambda-bd-lst) :exec lambda-bd-lst))
         (term (mbe :logic (pseudo-term-fix term) :exec term))
         ((unless (consp lambda-bd-lst)) term)
         ((cons first-bd rest-bd) lambda-bd-lst)
         ((lambda-binding b) first-bd))
      (generate-lambda-bindings rest-bd
                                `((lambda ,b.formals ,term) ,@b.actuals))))

  (defprod fhg-single-args
    ((fn func-p :default nil)
     (actuals pseudo-term-listp :default nil)
     (fn-hint-acc hint-pair-listp :default nil)
     (lambda-acc lambda-binding-listp :default nil)))

  (defthm symbol-listp-of-append-of-symbol-listp
    (implies (and (symbol-listp x) (symbol-listp y))
             (symbol-listp (append x y))))

  ;; Precondition:
  ;; 1. formals are in the right sequence as the functions are first defined
  ;; 2. all free vars in the thm of hypo must either be the formals or returns
  ;; These precondition should be satisfied when generating
  ;;   Smtlink-hint.
  (define generate-fn-hint-pair ((hypo hint-pair-p) (args fhg-single-args-p))
    :returns (fn-hint-pair hint-pair-p)
    :enabled t
    :guard-debug t
    (b* ((hypo (mbe :logic (hint-pair-fix hypo) :exec hypo))
         (args (mbe :logic (fhg-single-args-fix args) :exec args))
         ((hint-pair h) hypo)
         ((fhg-single-args a) args)
         ((func f) a.fn)

         (formals f.flattened-formals)
         (returns f.flattened-returns)
         ((unless (equal (len returns) 1))
          (prog2$ (er hard? 'SMT-goal-generator=>generate-fn-hint-pair "User defined function with more than one returns is not supported currently. ~%The function ~q0 has returns ~q1." f.name returns)
                  (make-hint-pair)))
         ((unless (equal (len formals) (len a.actuals)))
          (prog2$ (er hard? 'SMT-goal-generator=>generate-fn-hint-pair "Number of formals and actuals don't match. ~%Formals: ~q0, actuals: ~q1." formals a.actuals)
                  (make-hint-pair)))
         ((if (equal f.name 'quote))
          (prog2$ (er hard? 'SMT-goal-generator=>generate-fn-hint-pair "Function name can't be 'quote.")
                  (make-hint-pair)))

         (lambdaed-fn-call-instance (generate-lambda-bindings a.lambda-acc `(,f.name ,@a.actuals))))
      (change-hint-pair h
                        :thm `((lambda (,@formals ,@returns) ,h.thm)
                               ,@a.actuals ,lambdaed-fn-call-instance))))


  (define generate-fn-returns-hint ((returns decl-listp) (args fhg-single-args-p))
    :returns (fn-hint-lst hint-pair-listp)
    :measure (len returns)
    :enabled t
    (b* ((returns (mbe :logic (decl-list-fix returns) :exec returns))
         (args (mbe :logic (fhg-single-args-fix args) :exec args))
         ((fhg-single-args a) args)
         ((unless (consp returns)) a.fn-hint-acc)
         ((cons first rest) returns)
         ((decl d) first)
         ((hint-pair h) d.type)
         (hypo (change-hint-pair h :thm `(,h.thm ,d.name)))
         (first-hint-pair (generate-fn-hint-pair hypo args)))
      (generate-fn-returns-hint rest
                                (change-fhg-single-args a :fn-hint-acc (cons first-hint-pair a.fn-hint-acc)))))

  (define generate-fn-more-returns-hint ((more-returns hint-pair-listp) (args fhg-single-args-p))
    :returns (fn-hint-lst hint-pair-listp)
    :measure (len more-returns)
    :enabled t
    (b* ((more-returns (mbe :logic (hint-pair-list-fix more-returns) :exec more-returns))
         (args (mbe :logic (fhg-single-args-fix args) :exec args))
         ((fhg-single-args a) args)
         ((unless (consp more-returns)) a.fn-hint-acc)
         ((cons first rest) more-returns)
         (first-hint-pair (generate-fn-hint-pair first args)))
      (generate-fn-more-returns-hint rest
                                     (change-fhg-single-args a :fn-hint-acc (cons first-hint-pair a.fn-hint-acc)))))

  (define generate-fn-hint ((args fhg-single-args-p))
    :returns (fn-hint-lst hint-pair-listp)
    :enabled t
    (b* ((args (mbe :logic (fhg-single-args-fix args) :exec args))
         ((fhg-single-args a) args)
         ((func f) a.fn)
         ((unless f.uninterpreted)
          (prog2$ (er hard? 'SMT-goal-generator=>generate-fn-hint "Function call ~q0 still exists in term but it's not declared as an uninterpreted function." f.name)
                  a.fn-hint-acc))
         (fn-hint-acc-1 nil
                        ;; Disabling returns hint for now. See comments about
                        ;; basic functions in SMT-translator.lisp.
                        ;;(generate-fn-returns-hint f.returns a)
                        ))
      (generate-fn-more-returns-hint f.more-returns (change-fhg-single-args a :fn-hint-acc fn-hint-acc-1))))


  ;; function hypotheses generation arguments
  (defprod fhg-args
    ((term-lst pseudo-term-listp :default nil)
     (fn-lst func-alistp :default nil)
     (fn-hint-acc hint-pair-listp :default nil)
     (lambda-acc lambda-binding-listp :default nil)))


  (encapsulate ()

    (local (defthm lemma-1
             (implies (fhg-args-p x)
                      (pseudo-term-listp (fhg-args->term-lst x)))))

    (local (defthm lemma-2
             (implies (and (pseudo-term-listp y) (consp y))
                      (pseudo-termp (car y)))))

    (local (defthm lemma-3
             (implies (and (pseudo-termp z) (consp z) (not (equal (car z) 'quote)))
                      (pseudo-term-listp (cdr z)))))

    (local (defthm not-symbolp-then-consp-of-pseudo-termp
             (implies (and (pseudo-termp x)
                           (not (symbolp x)))
                      (consp x))))

    (defthm not-symbolp-then-consp-of-car-of-fhg-args->term-lst
      (implies (and (fhg-args-p args)
                    (consp (fhg-args->term-lst args))
                    (not (symbolp (car (fhg-args->term-lst args)))))
               (consp (car (fhg-args->term-lst args)))))

    (local (defthm lemma-4
             (implies (and (pseudo-term-listp y) (consp y))
                      (pseudo-term-listp (cdr y)))))

    (defthm pseudo-term-listp-of-cdr-of-fhg-args->term-lst
      (implies (and (fhg-args-p args)
                    (consp (fhg-args->term-lst args)))
               (pseudo-term-listp (cdr (fhg-args->term-lst args)))))

    (defthm pseudo-term-listp-of-cdar-of-fhg-args->term-lst
      (implies (and (fhg-args-p args)
                    (consp (fhg-args->term-lst args))
                    (not (symbolp (car (fhg-args->term-lst args))))
                    (not (equal (car (car (fhg-args->term-lst args)))
                                'quote)))
               (pseudo-term-listp (cdr (car (fhg-args->term-lst args))))))

    (local (defthm lemma-5
             (implies (and (pseudo-termp z)
                           (not (symbolp z)) (not (pseudo-lambdap (car z))))
                      (symbolp (car z)))
             :hints (("Goal" :in-theory (enable pseudo-termp pseudo-lambdap)))))

    (defthm symbolp-of-caar-of-fhg-args->term-lst
      (implies (and (fhg-args-p args)
                    (consp (fhg-args->term-lst args))
                    (not (symbolp (car (fhg-args->term-lst args))))
                    (not (pseudo-lambdap (car (car (fhg-args->term-lst args))))))
               (symbolp (car (car (fhg-args->term-lst args))))))

    (local (defthm lemma-6
             (implies (and (pseudo-termp x) (pseudo-lambdap (car x)))
                      (equal (len (cadar x)) (len (cdr x))))
             :hints (("Goal" :in-theory (enable pseudo-lambdap pseudo-termp)))))

    (defthm len-equal-of-formals-of-pseudo-lambdap-and-actuals-of-pseudo-termp-of-car-of-fhg-args->term-lst
      (implies (and (fhg-args-p args)
                    (consp (fhg-args->term-lst args))
                    (pseudo-lambdap (car (car (fhg-args->term-lst args)))))
               (equal (len (cadr (car (car (fhg-args->term-lst args)))))
                      (len (cdr (car (fhg-args->term-lst args)))))))
    )


  ;;
  ;; The hypotheses each function is going to generate:
  ;;
  ;; If it is a non-recursive function:
  ;; No hypotheses needed because the function doesn't exist anymore.
  ;; If there's a case where one needs hypotheses for non-recursive functions,
  ;;   I will be interested to know.
  ;;
  ;; If it is a recursive function, but not declared as uninterpreted:
  ;;   An error will be produced when Smtlink gets to the translator.
  ;;   The expander doesn't know enough information.
  ;;
  ;; If it is a uninterpreted function:
  ;;   Generate hypotheses for return type theorems and more return
  ;;     theorems.
  ;;
  (define generate-fn-hint-lst ((args fhg-args-p))
    :short "@(call generate-fn-hint-lst) generate auxiliary hypotheses from function expansion"
    :returns (fn-hint-lst hint-pair-listp)
    :measure (acl2-count (fhg-args->term-lst args))
    :verify-guards nil
    (b* ((args (mbe :logic (fhg-args-fix args) :exec args))
         ;; Syntactic sugar for easy field access, e.g. a.term-lst
         ((fhg-args a) args)
         ((unless (consp a.term-lst)) a.fn-hint-acc)
         ((cons term rest) a.term-lst)
         ;; If first term is an symbolp, return the symbol
         ;; then recurse on the rest of the list
         ((if (symbolp term))
          (generate-fn-hint-lst (change-fhg-args a :term-lst rest)))
         ((if (equal (car term) 'quote))
          (generate-fn-hint-lst (change-fhg-args a :term-lst rest)))
         ;; The first term is now a function call:
         ;; Cons the function call and function actuals out of term
         ((cons fn-call fn-actuals) term)

         ;; If fn-call is a pseudo-lambdap, update lambda-binding-lst
         ((if (pseudo-lambdap fn-call))
          (b* ((lambda-formals (lambda-formals fn-call))
               (lambda-body (lambda-body fn-call))
               (lambda-actuals fn-actuals)
               (lambda-bd (make-lambda-binding :formals lambda-formals :actuals lambda-actuals))
               ((unless (mbt (lambda-binding-p lambda-bd))) a.fn-hint-acc)
               (fn-hint-acc-1
                (generate-fn-hint-lst (change-fhg-args a
                                                       :term-lst (list lambda-body)
                                                       :lambda-acc (cons lambda-bd a.lambda-acc))))
               (fn-hint-acc-2
                (generate-fn-hint-lst (change-fhg-args a
                                                       :term-lst lambda-actuals
                                                       :fn-hint-acc fn-hint-acc-1))))
            (generate-fn-hint-lst (change-fhg-args a
                                                   :term-lst rest
                                                   :fn-hint-acc fn-hint-acc-2))))

         ;; If fn-call is neither a lambda expression nor a function call
         ((unless (mbt (symbolp fn-call))) a.fn-hint-acc)
         ;; Try finding function call from fn-lst
         (fn (hons-get fn-call a.fn-lst))
         ;; If fn-call doesn't exist in fn-lst, it can be a basic function,
         ;; in that case we don't do anything with it.
         ;; Otherwise it can be a function that's forgotten to be added to fn-lst.
         ;; The translator will fail to translate it and report an error.
         ((unless fn)
          (b* ((fn-hint-acc-1 (generate-fn-hint-lst (change-fhg-args a :term-lst fn-actuals))))
            (generate-fn-hint-lst (change-fhg-args a :term-lst rest :fn-hint-acc fn-hint-acc-1))))

         ;; Now fn is a function in fn-lst,
         ;;   we need to generate returns and more-returns hypotheses for them
         ((func f) (cdr fn))
         (fn-hint-acc-1 (generate-fn-hint (make-fhg-single-args :fn f
                                                                :actuals fn-actuals
                                                                :fn-hint-acc a.fn-hint-acc
                                                                :lambda-acc a.lambda-acc)))
         (fn-hint-acc-2
          (generate-fn-hint-lst (change-fhg-args a
                                                 :term-lst fn-actuals
                                                 :fn-hint-acc fn-hint-acc-1)))
         )
      (generate-fn-hint-lst (change-fhg-args a
                                             :term-lst rest
                                             :fn-hint-acc fn-hint-acc-2))))

  (verify-guards generate-fn-hint-lst)


  ;; ---------------------------------------------------------------------
  ;; TODO
  ;; Should this function be in this file?
  (define is-type-decl ((type pseudo-termp))
    :returns (is? booleanp)
    :enabled t
    (b* ((type (mbe :logic (pseudo-term-fix type) :exec type))
         ((unless (consp type)) nil))
      (and (equal (len type) 2)
           (symbolp (car type))
           (symbolp (cadr type)))))

  ;; --------------------------------------------------------------------

  (define structurize-type-decl-list ((type-decl-list pseudo-term-listp))
    :returns (structured-decl-list decl-listp)
    :guard-debug t
    (b* ((type-decl-list (mbe :logic (pseudo-term-list-fix type-decl-list) :exec type-decl-list))
         ((unless (consp type-decl-list)) nil)
         ((cons first rest) type-decl-list)
         ((unless (is-type-decl first))
          (er hard? 'SMT-goal-generator=>structurize-type-decl-list "Non type declaration found: ~q0" first))
         ((list type name) first))
      (cons (make-decl :name name :type (make-hint-pair :thm type))
            (structurize-type-decl-list rest))))

  (encapsulate ()
    (local (in-theory (enable pseudo-term-listp-of-expand
                              hint-pair-listp-of-generate-fn-hint-lst
                              hint-pair-listp-of-generate-hyp-hint-lst)))

    (local (defthm pseudo-termp-of-disjoin-of-pseudo-term-listp
             (implies (pseudo-term-listp cl)
                      (pseudo-termp (disjoin cl)))))

    (local (defthm hint-pair-listp-of-append
             (implies (and (hint-pair-listp x) (hint-pair-listp y))
                      (hint-pair-listp (append x y)))))

    ;; The top level function for generating SMT goals: G-prim and A's
    (define SMT-goal-generator ((cl pseudo-term-listp) (hints smtlink-hint-p) state)
      :returns (new-hints smtlink-hint-p)
      :short "@(call SMT-goal-generator) is the top level function for generating SMT goals: G-prim and A's"
      :guard-debug t
      :verify-guards nil
      (b* ((cl (mbe :logic (pseudo-term-list-fix cl) :exec cl))
           (hints (mbe :logic (smtlink-hint-fix hints) :exec hints))
           ((smtlink-hint h) hints)
           ;; Make an alist version of fn-lst
           (fn-lst (make-alist-fn-lst h.functions))
           (fn-lvls (initialize-fn-lvls fn-lst))

           ;; Generate user given hypotheses and their hints from hyp-lst
           (hyp-hint-lst (with-fast-alist fn-lst (generate-hyp-hint-lst h.hypotheses fn-lst fn-lvls state)))

           ;; Expand main clause using fn-lst
           ;; Generate function hypotheses and their hints from fn-lst
           (G-prim
            (with-fast-alist fn-lst (car (expand (make-ex-args
                                                  :term-lst (list (disjoin cl))
                                                  :fn-lst fn-lst
                                                  :fn-lvls fn-lvls)
                                                 state))))

           ;; Generate auxiliary hypotheses from function expansion
           (fn-hint-lst (with-fast-alist fn-lst (generate-fn-hint-lst (make-fhg-args
                                                                       :term-lst (list G-prim)
                                                                       :fn-lst fn-lst
                                                                       :fn-hint-acc nil
                                                                       :lambda-acc
                                                                       nil))))

           ;; Generate auxiliary hypotheses for type extraction
           ((mv type-decl-list G-prim-without-type) (SMT-extract G-prim))
           (structured-decl-list (structurize-type-decl-list type-decl-list))

           ;; Combine all auxiliary hypotheses
           (total-aux-hint-lst `(,@fn-hint-lst ,@hyp-hint-lst))

           ;; Combine expanded main clause and its hint
           (expanded-clause-w/-hint (make-hint-pair :thm G-prim-without-type :hints h.main-hint))

           ;; Update smtlink-hint
           (new-hints
            (change-smtlink-hint hints
                                 :fast-functions fn-lst
                                 :aux-hint-list total-aux-hint-lst
                                 :type-decl-list structured-decl-list
                                 :expanded-clause-w/-hint expanded-clause-w/-hint
                                 )))
        new-hints))
    (verify-guards SMT-goal-generator)
    )

  )

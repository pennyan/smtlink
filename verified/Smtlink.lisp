;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software
;;

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/basic/inductions" :dir :system)
(include-book "std/basic/defs" :dir :system)

(include-book "SMT-hint-interface")
(include-book "SMT-verified-cps")
(include-book "SMT-config")

;; (defsection Smtlink-process-user-hint
;;   :parents (Smtlink)
;;   :short "Functionalities for processing user hints given to Smtlink. User
;;   hints will be merged with (smt-hint)."

  ;; --------------------------------------------------------

  ;; Example:
  ;; :hints (("Goal"
  ;;          :clause-processor
  ;;          (SMT::smtlink clause
  ;;                        '(:functions ((f0 :formals ((a0 rationalp))
  ;;                                          :returns (r0 rationalp :hints (:use ((:instance returns-lemma))))
  ;;                                          :level 1
  ;;                                          :guard ((> a0 0) :hints (:use ((:instance guard-lemma))))
  ;;                                          :more-returns (((> r0 0) :hints (:use ((:instance more-lemma)))))))
  ;;                          :hypotheses (((> a b) :hints (:use ((:instance lemma)))))
  ;;                          :main-hint (:use ((:instance thm1)))
  ;;                          :int-to-rat nil
  ;;                          :smt-fname ""
  ;;                          :rm-file t
  ;;                          :smt-solver-params (...)
  ;;                          :smt-solver-cnf ()))))

  ;; Types:
  ;; qbooleanp/fix
  ;; qnatp/fix
  ;; qstringp/fix
  ;; hints-syntax-p/fix
  ;; hypothesis-syntax-p/fix
  ;; hypothesis-lst-syntax-p/fix
  ;; argument-syntax-p/fix
  ;; argument-lst-syntax-p/fix
  ;; function-option-syntax-p/fix
  ;; function-option-lst-syntax-p/fix
  ;; function-syntax-p/fix
  ;; function-lst-syntax-p/fix
  ;; smt-solver-cnf-p/fix
  ;; smt-solver-params-p/fix
  ;; smtlink-hint-syntax-p/fix

  (define qstringp ((term t))
    :returns (syntax-good? booleanp)
    :short "Recognizer for a quoted stringp."
    (and (true-listp term)
         (car term) (cadr term) (not (cddr term))
         (equal (car term) 'quote)
         (stringp (cadr term))))

  (define qstring-fix ((term qstringp))
    :short "Fixing function for a qstringp."
    :returns (fixed-term qstringp)
    (mbe :logic (if (qstringp term) term ''"")
         :exec term))

  (defthm qstring-fix-idempotent-lemma
    (equal (qstring-fix (qstring-fix x))
           (qstring-fix x))
    :hints (("Goal" :in-theory (enable qstring-fix))))

  ;; This one shows that it's possible to connect fixing function and
  ;; the type functions together, and became useful for other defprods, etc.
  ;; Since I'm currently not using defprods for others either, this is probably
  ;; not that useful. However, this deffixtype shows as an example for future
  ;; necessity.
  (deffixtype qstring
    :pred  qstringp
    :fix   qstring-fix
    :equiv qstring-equiv
    :define t
    :forward t
    :topic qstringp)

  (define qnatp ((term t))
    :returns (syntax-good? booleanp)
    :short "Recognizer for a quoted qnatp."
    (and (true-listp term)
         (car term) (cadr term) (not (cddr term))
         (equal (car term) 'quote)
         (natp (cadr term))))

  (define qnat-fix ((term qnatp))
    :returns (fixed-term qnatp)
    :short "Fixing function for a qnatp."
    (mbe :logic (if (qnatp term) term ''0)
         :exec term))

  (defthm qnat-fix-idempotent-lemma
    (equal (qnat-fix (qnat-fix x))
           (qnat-fix x))
    :hints (("Goal" :in-theory (enable qnat-fix))))

  (deffixtype qnat
    :pred  qnatp
    :fix   qnat-fix
    :equiv qnat-equiv
    :define t
    :forward t
    :topic qnatp)

  (define qbooleanp ((term t))
    :short "Recognizer for a quoted booleanp."
    :returns (syntax-good? booleanp)
    (and (true-listp term)
         (car term)
         (equal (car term) 'quote)
         (booleanp (cadr term))))

  (define qboolean-fix ((term qbooleanp))
    :returns (fixed-term qbooleanp)
    :short "Fixing function for a qbooleanp."
    (mbe :logic (if (qbooleanp term) term ''nil)
         :exec term))

  (defthm qboolean-fix-idempotent-lemma
    (equal (qboolean-fix (qboolean-fix x))
           (qboolean-fix x))
    :hints (("Goal" :in-theory (enable qboolean-fix))))

  (deffixtype qboolean
    :pred  qbooleanp
    :fix   qboolean-fix
    :equiv qboolean-equiv
    :define t
    :forward t
    :topic qbooleanp)

  (define hints-syntax-p ((term t))
    :returns (syntax-good? booleanp)
    :short "Recognizer for hints-syntax."
    (true-listp term))

  (define hints-syntax-fix ((term hints-syntax-p))
    :returns (fixed-term hints-syntax-p)
    :short "Fixing function for a hints-sytnax-p."
    (mbe :logic (if (hints-syntax-p term) term nil)
         :exec term))

  (define hypothesis-syntax-p ((term t))
    :returns (syntax-good? booleanp)
    :short "Recognizer for hypothesis-syntax."
    (or (and (atom term)
             (equal term nil))
        ;; Without hints
        (and (true-listp term)
             (car term) (not (cdr term))
             (pseudo-termp (car term)))
        ;; With hints
        (and (true-listp term)
             (car term) (cadr term) (not (cdddr term))
             (pseudo-termp (car term))
             (equal (cadr term) ':hints)
             (hints-syntax-p (caddr term))))
    ///
    (defthm true-listp-of-caddr
      (implies
       (and (consp term)
            (consp (cdr term))
            (true-listp (cddr term))
            (equal (+ 2 (len (cddr term))) 3)
            (pseudo-termp (car term))
            (equal (cadr term) :hints)
            (hints-syntax-p (caddr term)))
       (true-listp (caddr term)))
      :hints (("Goal" :in-theory (enable hints-syntax-p)))))

  (define hypothesis-syntax-fix ((term hypothesis-syntax-p))
    :returns (fixed-term hypothesis-syntax-p)
    :short "Fixing function for a hypothesis-syntax-p."
    (mbe :logic (if (hypothesis-syntax-p term) term nil)
         :exec term))

  (defthm hypothesis-syntax-fix-idempotent-lemma
    (equal (hypothesis-syntax-fix (hypothesis-syntax-fix x))
           (hypothesis-syntax-fix x))
    :hints (("Goal" :in-theory (enable hypothesis-syntax-fix))))

  (deffixtype hypothesis-syntax
    :pred  hypothesis-syntax-p
    :fix   hypothesis-syntax-fix
    :equiv hypothesis-syntax-equiv
    :define t
    :forward t
    :topic hypothesis-syntax-p)

  (define hypothesis-lst-syntax-p ((term t))
    :returns (syntax-good? booleanp)
    :short "Recognizer for hypothesis-lst-syntax."
    (b* (((if (atom term)) (equal term nil))
         ((cons first rest) term)
         (- (cw "hypo first: ~q0" first))
         (- (cw "(hypothesis-syntax-p first): ~q0" (hypothesis-syntax-p first))))
      (and (hypothesis-syntax-p first)
           (hypothesis-lst-syntax-p rest)))
    ///
    (defthm true-listp-of-hypothesis-lst-syntax
      (implies (hypothesis-lst-syntax-p x)
               (true-listp x))))

  (define hypothesis-lst-syntax-fix ((term hypothesis-lst-syntax-p))
    :returns (fixed-term hypothesis-lst-syntax-p
                         :hints (("Goal"
                                  :in-theory (enable hypothesis-lst-syntax-p))))
    :verify-guards nil
    :short "Fixing function for a hypothesis-lst-syntax-p."
    (mbe :logic (if (consp term)
                    (cons (hypothesis-syntax-fix (car term))
                          (hypothesis-lst-syntax-fix (cdr term)))
                  nil)
         :exec term))

  (verify-guards hypothesis-lst-syntax-fix
    :hints (("Goal" :in-theory (enable hypothesis-syntax-fix
                                       hypothesis-lst-syntax-p hypothesis-lst-syntax-fix))))

  (defthm hypothesis-lst-syntax-fix-idempotent-lemma
    (equal (hypothesis-lst-syntax-fix (hypothesis-lst-syntax-fix x))
           (hypothesis-lst-syntax-fix x))
    :hints (("Goal" :in-theory (enable hypothesis-lst-syntax-fix hypothesis-syntax-fix))))

  (deffixtype hypothesis-lst-syntax
    :pred  hypothesis-lst-syntax-p
    :fix   hypothesis-lst-syntax-fix
    :equiv hypothesis-lst-syntax-equiv
    :define t
    :forward t
    :topic hypothesis-lst-syntax-p)

  (define smt-typep ((term t))
    :returns (valid-type? booleanp)
    :short "Types allowed in Smtlink."
    (if (member-equal term
                      ' (rationalp realp real/rationalp booleanp integerp))
        t nil))

  (define argument-syntax-p ((term t))
    :returns (syntax-good? booleanp)
    :short "Recognizer for argument-syntax."
    (or (and (atom term)
             (equal term nil))
        ;; Just the name
        (and (true-listp term)
             (car term) (not (cdr term))
             (symbolp (car term)))
        ;; The name and the type/guard
        (and (true-listp term)
             (car term) (cadr term) (not (cddr term))
             (smt-typep (car term))
             (symbolp (cadr term)))
        ;; The name, the type and the :hints
        (and (true-listp term)
             (car term) (cadr term) (not (cdddr term)) 
             (symbolp (car term))
             (smt-typep (cadr term))
             (hints-syntax-p (cddr term)))))

  (define argument-syntax-fix ((term argument-syntax-p))
    :returns (fixed-term argument-syntax-p)
    :short "Fixing function for argument-syntax-p."
    (mbe :logic (if (argument-syntax-p term) term nil)
         :exec term))

  (define argument-lst-syntax-p ((term t))
    :short "Recognizer for argument-lst-syntax."
    :returns (syntax-good? booleanp)
    (b* (((if (atom term)) (equal term nil))
         ((cons first rest) term))
      (and (argument-syntax-p first)
           (argument-lst-syntax-p rest))))

  (defthm argument-syntax-fix-idempotent-lemma
    (equal (argument-syntax-fix (argument-syntax-fix x))
           (argument-syntax-fix x))
    :hints (("Goal" :in-theory (enable argument-syntax-fix))))

  (deffixtype argument-syntax
    :pred  argument-syntax-p
    :fix   argument-syntax-fix
    :equiv argument-syntax-equiv
    :define t
    :forward t
    :topic argument-syntax-p)


  (define argument-lst-syntax-fix ((term argument-lst-syntax-p))
    :short "Fixing function for argument-lst-syntax."
    :returns (fixed-term argument-lst-syntax-p
                         :hints (("Goal"
                                  :in-theory (enable argument-lst-syntax-p))))
    :verify-guards nil
    (mbe :logic (if (consp term)
                    (cons (argument-syntax-fix (car term))
                          (argument-lst-syntax-fix (cdr term)))
                  nil)
         :exec term))
  (verify-guards argument-lst-syntax-fix
    :hints (("Goal"
             :in-theory (enable argument-lst-syntax-fix argument-syntax-fix argument-lst-syntax-p))))

  (defthm argument-lst-syntax-fix-idempotent-lemma
    (equal (argument-lst-syntax-fix (argument-lst-syntax-fix x))
           (argument-lst-syntax-fix x))
    :hints (("Goal" :in-theory (enable argument-lst-syntax-fix argument-syntax-fix))))

  (deffixtype argument-lst-syntax
    :pred  argument-lst-syntax-p
    :fix   argument-lst-syntax-fix
    :equiv argument-lst-syntax-equiv
    :define t
    :forward t
    :topic argument-lst-syntax-p)

  (defconst *function-options*
    '((:formals . argument-lst-syntax-p)
      (:returns . argument-lst-syntax-p)
      (:level . natp)
      (:guard . hypothesis-syntax-p)
      (:more-returns . hypothesis-lst-syntax-p)))

  (defconst *function-option-names*
    (strip-cars *function-options*))

  (defconst *function-option-types*
    (remove-duplicates-equal (strip-cdrs *function-options*)))

  (define function-option-type-p ((option-type t))
    :returns (syntax-good? booleanp)
    :short "Recoginizer for function-option-type."
    (if (member-equal option-type *function-option-types*) t nil))

  (define function-option-type-fix ((option-type function-option-type-p))
    :returns (fixed-option-type function-option-type-p
                                :hints (("Goal" :in-theory (enable
                                                            function-option-type-p ))))
    :short "Fixing function for function-option-type."
    (mbe :logic (if (function-option-type-p option-type) option-type 'natp)
         :exec option-type))

  (define function-option-name-p ((option-name t))
    :returns (syntax-good? booleanp)
    :short "Recoginizer for an function-option-name."
    (if (member-equal option-name *function-option-names*) t nil))

  ;; This default value ':formals will generate a list of options with
  ;; the same value. This violates the constraint that options should be
  ;; distinctive. But that's alright, since we never expect option-fix's logic
  ;; formula to ever get used. Proved guards ensure it.
  (define function-option-name-fix ((option-name function-option-name-p))
    :returns (fixed-option-name function-option-name-p)
    :short "Fixing function for option."
    (mbe :logic (if (function-option-name-p option-name) option-name ':formals)
         :exec option-name))

(local (in-theory (enable function-option-name-fix)))
(deffixtype function-option-name
  :pred  function-option-name-p
  :fix   function-option-name-fix
  :equiv function-option-name-equiv
  :define t
  :forward t
  :topic function-option-name-p)

(deflist function-option-name-lst
  :elt-type function-option-name
  :true-listp t)

  ;; (define function-option-name-lst-p ((option-lst t))
  ;;   :returns (syntax-good? booleanp)
  ;;   :short "Recoginizer for option-lst."
  ;;   (b* (((if (atom option-lst)) (equal option-lst nil))
  ;;        ((cons first rest) option-lst))
  ;;     (and (function-option-name-p first)
  ;;          (function-option-name-lst-p rest))))

  ;; (define function-option-name-lst-fix ((option-lst function-option-name-lst-p))
  ;;   :returns (fixed-option-lst function-option-name-lst-p
  ;;                              :hints (("Goal" :in-theory (enable function-option-name-lst-p))))
  ;;   :short "Fixing function for option-name-lst."
  ;;   :verify-guards nil
  ;;   (mbe :logic (if (atom option-lst)
  ;;                   nil
  ;;                 (cons (function-option-name-fix (car option-lst))
  ;;                       (function-option-name-lst-fix (cdr option-lst))))
  ;;        :exec option-lst))
  ;; (verify-guards function-option-name-lst-fix
  ;;   :hints (("Goal" :in-theory (enable function-option-name-fix
  ;;                                      function-option-name-lst-fix
  ;;                                      function-option-name-p function-option-name-lst-p))))

  ;; The conditions in eval-type should go along with *function-options*
  (define eval-function-option-type ((option-type function-option-type-p) (term t))
    :returns (type-correct? booleanp)
    :short "Evaluating types for function option body."
    (b* ((option-type (function-option-type-fix option-type)))
      (case option-type
        (argument-lst-syntax-p (argument-lst-syntax-p term))
        (natp (natp term))
        (hypothesis-syntax-p (hypothesis-syntax-p term))
        (t (hypothesis-lst-syntax-p term)))))

  (define function-option-syntax-p ((term t) (used function-option-name-lst-p))
    :returns (mv (syntax-good? booleanp)
                 (used? function-option-name-lst-p
                        :hints (("Goal" :in-theory (enable function-option-name-lst-p function-option-name-p)))))
    :short "Recoginizer for function-option-syntax."
    :verify-guards nil
    (b* ((used (function-option-name-lst-fix used))
         ((if (equal term nil)) (mv t used))
         ((unless (and (true-listp term) (car term) (not (cddr term)))) (mv nil used))
         ((cons option body-lst) term)
         ((unless (function-option-name-p option)) (mv nil used))
         (option-type (cdr (assoc-equal option *function-options*))))
      (mv (and (not (member-equal option used))
               (eval-function-option-type option-type (car body-lst)))
          (cons option used))))
  (verify-guards function-option-syntax-p
    :guard-debug t
    :hints (("Goal" :in-theory (enable function-option-syntax-p function-option-name-p
                                       eval-function-option-type function-option-name-lst-p))))

  ;; (define exist-odd-lst ((key symbolp) (lst t))
  ;;   :returns (exist? booleanp)
  ;;   :short "Test if key exist in lst on the odd positions (with position staring
  ;; from 1)"
  ;;   :measure (len lst)
  ;;   :hints (("Goal" :in-theory (enable true-list-fix)))
  ;;   :verify-guards nil
  ;;   (b* ((key (symbol-fix key))
  ;;        ((if (equal lst nil)) nil)
  ;;        ((unless (and (true-listp lst) (>= (len lst) 2))) nil)
  ;;        ((list* first & rest) lst)
  ;;        ((if (equal first key)) t))
  ;;     (exist-odd-lst key rest)))
  ;; (verify-guards exist-odd-lst
  ;;   :hints (("Goal" :in-theory (enable true-list-fix))))

(define function-option-lst-syntax-p-helper ((term t) (used function-option-name-lst-p))
    :returns (syntax-good? booleanp)
    :short "Helper for function-option-lst-syntax-p."
    (b* (((if (atom term)) (equal term nil))
         ((unless (and (true-listp term) (>= (len term) 2))) nil)
         ((list* first second rest) term)
         (- (cw "first: ~q0" first))
         (- (cw "second: ~q0" second))
         ((mv res new-used) (function-option-syntax-p (list first second)
                                                      used))
         (- (cw "res: ~q0" res))
         (- (cw "booleanp? ~q0" (booleanp second))))
      (and res (function-option-lst-syntax-p-helper rest new-used)))
    ///
    (defthm function-option-lst-syntax-p-constraint
      (implies (and (function-option-lst-syntax-p-helper fun-opt-lst any)
                    (consp fun-opt-lst))
               (or (equal (car fun-opt-lst) ':formals)
                   (equal (car fun-opt-lst) ':returns)
                   (equal (car fun-opt-lst) ':level)
                   (equal (car fun-opt-lst) ':guard)
                   (equal (car fun-opt-lst) ':more-returns)))
      :hints (("Goal"
               :in-theory (enable eval-function-option-type
                                  function-option-syntax-p
                                  function-option-name-p))))

    (defthm function-option-lst-syntax-p-of-option
      (implies
       (and (consp (cdr fun-opt-lst))
            (function-option-lst-syntax-p-helper fun-opt-lst nil)
            (consp fun-opt-lst))
       (and (implies (equal (car fun-opt-lst) ':formals)
                     (argument-lst-syntax-p (cadr fun-opt-lst)))
            (implies (equal (car fun-opt-lst) ':returns)
                     (argument-lst-syntax-p (cadr fun-opt-lst)))
            (implies (equal (car fun-opt-lst) ':level)
                     (natp (cadr fun-opt-lst)))
            (implies (equal (car fun-opt-lst) ':guard)
                     (hypothesis-syntax-p (cadr fun-opt-lst)))
            (implies (equal (car fun-opt-lst) ':more-returns)
                     (hypothesis-lst-syntax-p (cadr fun-opt-lst)))))
      :hints (("Goal"
               :in-theory (enable function-option-syntax-p
                                  eval-function-option-type))))

    (defthm car-term-function-option-syntax-p
      (implies (and (consp term)
                    (function-option-lst-syntax-p-helper term used))
               (function-option-name-p (car term)))
      :hints (("Goal" :in-theory (enable function-option-syntax-p))))

    (defthm caddr-term-function-option-syntax-p
      (implies (and (consp (cddr term))
                    (not (function-option-name-p (caddr term)))
                    (function-option-lst-syntax-p-helper (cddr term) used))
               (not (caddr term)))
      :hints (("Goal" :in-theory (enable function-option-syntax-p))))
    )

(define list-containment ((list1 true-listp) (list2 true-listp))
  :returns (p booleanp)
  (b* (((unless (consp list1)) t)
       ((unless (consp list2)) nil)
       ((cons hd tl) list1))
    (and (member-equal hd list2) (list-containment tl list2))))
(defthm member-when-list-containment
  (implies (and (true-listp list1) (true-listp list2)
                (list-containment list1 list2)
                (member-equal x list1))
           (member-equal x list2))
  :hints(("Goal" :in-theory (enable list-containment))))
(defthm list-containment-of-cons
  (implies (and (true-listp list1) (true-listp list2)
                (list-containment list1 list2))
           (list-containment (cons x list1) (cons x list2)))
  :hints(("Goal" :in-theory (enable list-containment))))
(defthm list-containment-of-append
  (implies (and (true-listp list1a) (true-listp list1b)
                (true-listp list2a) (true-listp list2b) ; or not to be?
                (list-containment list1a list2a)
                (list-containment list1b list2b))
           (list-containment (append list1a list1b)
                             (append list2a list2b)))
  :hints(("Goal" :in-theory (enable list-containment))))

(defthm lemma-1
  (implies (and (function-option-name-lst-p used)
                (assoc-equal opt *function-options*)
                (eval-function-option-type (cdr (assoc-equal opt
                                                             *function-options*))
                                           val))
           (iff (mv-nth 0 (function-option-syntax-p (list opt val) used))
                (not (member-equal opt used))))
  :hints(("Goal" :in-theory (enable function-option-syntax-p))))

  (defthm lemma-2
    (implies (and (function-option-name-lst-p used)
                  (function-option-name-p new-opt)
                  (mv-nth 0 (function-option-syntax-p (list opt val)
                                                      (cons new-opt used))))
             (mv-nth 0 (function-option-syntax-p (list opt val) used)))
    :hints(("Goal" :in-theory (enable function-option-syntax-p))))

(defthm lemma-3
  (implies (and (function-option-name-lst-p used)
                (mv-nth 0 (function-option-syntax-p (list opt val) used)))
           (equal (mv-nth 1 (function-option-syntax-p (list opt val) used))
                  (cons opt used)))
  :hints(("goal" :in-theory (enable function-option-syntax-p))))

(defthmd lemma-4
  (implies (and (function-option-name-lst-p used-1)
                (function-option-name-lst-p used-2)
                (list-containment used-1 used-2)
                (list-containment used-2 used-1))
           (iff (mv-nth 0 (function-option-syntax-p (list opt val)
                                                    used-1))
                (mv-nth 0 (function-option-syntax-p (list opt val)
                                                    used-2))))
  :hints(("Goal" :in-theory (enable function-option-syntax-p))))

(defthm lemma-5
  (implies (function-option-name-p option) (assoc-equal option *function-options*))
  :hints (("Goal" :in-theory (enable function-option-name-p))))

(defthm lemma-6
  (implies (and (function-option-name-lst-p used)
                (mv-nth 0 (function-option-syntax-p (list opt val) used)))
           (and (assoc-equal opt *function-options*)
                (eval-function-option-type (cdr (assoc-equal opt
                                                             *function-options*))
                                           val)
                (not (member-equal opt used))))
  :hints(("Goal" :in-theory (enable function-option-syntax-p))))

(defthm lemma-11
  (implies (and (function-option-name-lst-p used)
                (function-option-lst-syntax-p-helper term used)
                term)
           (and (assoc-equal (car term) *function-options*)
                (eval-function-option-type
                 (cdr (assoc-equal (car term) *function-options*))
                 (cadr term))
                (not (member-equal (car term) used))))
  :hints(("Goal" :expand (function-option-lst-syntax-p-helper term used)
          :in-theory (disable lemma-6)
          :use((:instance lemma-6 (opt (car term)) (val (cadr term)) (used used))))))

(defthmd lemma-12
  (implies (and (function-option-name-lst-p used-1)
                (function-option-name-lst-p used-2)
                (list-containment used-1 used-2)
                (list-containment used-2 used-1))
           (iff (function-option-lst-syntax-p-helper term used-1)
                (function-option-lst-syntax-p-helper term used-2)))
  :hints(("Goal" :in-theory (enable function-option-lst-syntax-p-helper))
         ("Subgoal *1/3"
          :use((:instance lemma-4
                          (used-1 used-1) (used-2 used-2)
                          (opt (car term)) (val (cadr term))))
          )
         ("Subgoal *1/2" :use((:instance lemma-4
                                         (used-1 used-1) (used-2 used-2)
                                         (opt (car term)) (val (cadr term)))))
         ))

(defthmd lemma-13
  (equal (list* x y z) (append (list x y ) z)))

(defthmd lemma-14 (list-containment (list x y) (list y x))
  :hints(("Goal" :in-theory (enable list-containment))))

(defthmd reflexivity-of-list-containment
  (implies (true-listp x) (list-containment x x)))

(defthmd lemma-15 ;; may need a :use hint for reflexivity-of-list-containment
  (implies (true-listp z)
           (list-containment (append (list x y) z) (append (list y x) z)))
  :hints(("Goal" :use((:instance lemma-14 (x x) (y y))
                      (:instance list-containment-of-append
                                 (list1a (list x y)) (list1b z)
                                 (list2a (list y x)) (list2b z))
                      (:instance reflexivity-of-list-containment (x z))))))

(defthm lemma-yan
  (implies (and (function-option-name-lst-p used-1)
                (function-option-name-lst-p used-2)
                (list-containment used-1 used-2)
                (list-containment used-2 used-1)
                (function-option-lst-syntax-p-helper term used-1))
           (function-option-lst-syntax-p-helper term used-2))
  :hints(("Goal" :in-theory (enable function-option-lst-syntax-p-helper)
          :use ((:instance lemma-12)))))

(defthm yan-2
  (implies (and
            (consp (cdr term))
            (true-listp (cddr term))
            (<= 2 (+ 2 (len (cddr term))))
            (function-option-name-lst-p used)
            (function-option-name-p new-opt)
            (mv-nth 0
                    (function-option-syntax-p (list (car term) (cadr term))
                                              (cons new-opt used)))
            (function-option-lst-syntax-p-helper (cddr term)
                                                 (list* (car term) new-opt
                                                        used)))
           (function-option-name-p (car term)))
  :hints (("Goal"
           :in-theory (enable function-option-lst-syntax-p-helper)
           :use ((:instance car-term-function-option-syntax-p
                            (used (cons new-opt used)))))))

(defthm yan-3
  (implies (and
            (consp (cdr term))
            (true-listp (cddr term))
            (<= 2 (+ 2 (len (cddr term))))
            (function-option-name-lst-p used)
            (function-option-name-p new-opt)
            (mv-nth 0
                    (function-option-syntax-p (list (car term) (cadr term))
                                              (cons new-opt used)))
            (function-option-lst-syntax-p-helper (cddr term)
                                                 (list* (car term) new-opt
                                                        used)))
           (function-option-name-lst-p (list* (car term) new-opt used))))

(defthm yan-4
  (implies (and
            (consp (cdr term))
            (true-listp (cddr term))
            (<= 2 (+ 2 (len (cddr term))))
            (function-option-name-lst-p used)
            (function-option-name-p new-opt)
            (mv-nth 0
                    (function-option-syntax-p (list (car term) (cadr term))
                                              (cons new-opt used)))
            (function-option-lst-syntax-p-helper (cddr term)
                                                 (list* (car term) new-opt
                                                        used)))
           (function-option-name-lst-p (list* new-opt (car term) used))))

(defthm yan-1
  (implies
   (and
    (consp (cdr term))
    (true-listp (cddr term))
    (<= 2 (+ 2 (len (cddr term))))
    (function-option-name-lst-p used)
    (function-option-name-p new-opt)
    (mv-nth 0
            (function-option-syntax-p (list (car term) (cadr term))
                                      (cons new-opt used)))
    (function-option-lst-syntax-p-helper (cddr term)
                                         (list* (car term) new-opt used)))
   (function-option-lst-syntax-p-helper (cddr term)
                                        (list* new-opt (car term) used)))
  :hints (("Goal"
           :use ((:instance lemma-3)
                 (:instance lemma-4)
                 (:instance lemma-yan
                            (term (cddr term))
                            (used-1 (list* (car term) new-opt used))
                            (used-2 (list* new-opt (car term) used)))
                 (:instance lemma-15 (x new-opt) (y (car term)) (z used))
                 (:instance lemma-15 (x (car term)) (y new-opt) (z used))))))

(defthm yan
  (implies
   (and
    (consp (cdr term))
    (true-listp (cddr term))
    (<= 2 (+ 2 (len (cddr term))))
    (not (function-option-lst-syntax-p-helper (cddr term)
                                              (list* new-opt (car term) used)))
    (function-option-name-lst-p used)
    (function-option-name-p new-opt)
    (mv-nth 0
            (function-option-syntax-p (list (car term) (cadr term))
                                      (cons new-opt used)))
    (function-option-lst-syntax-p-helper (cddr term)
                                         (list* (car term) new-opt used)))
   (function-option-lst-syntax-p-helper (cddr term)
                                        (cons (car term) used)))
  :hints (("Goal" :use ((:instance yan-1)))))

(defthm lemma-16
  (implies (and (function-option-name-lst-p used)
                (function-option-name-p new-opt)
                (function-option-lst-syntax-p-helper term (cons new-opt used)))
           (function-option-lst-syntax-p-helper term used))
  :hints(("Goal"
          :in-theory (enable function-option-lst-syntax-p-helper))))

     (defthm function-option-lst-syntax-preserve
       (implies (and (function-option-lst-syntax-p-helper term nil)
                     (consp term))
                (function-option-lst-syntax-p-helper (cddr term)
                                                     nil))
       :hints (("Goal"
                :in-theory (enable function-option-lst-syntax-p-helper)
                :use ((:instance lemma-16
                                 (term (cddr term))
                                 (new-opt (car term))
                                 (used nil))))))


  (define function-option-lst-syntax-p ((term t))
    :returns (syntax-good? booleanp)
    :short "Recogizer for function-option-lst-syntax"
    (function-option-lst-syntax-p-helper term nil))

  (define function-option-lst-syntax-fix ((term function-option-lst-syntax-p))
    :returns (fixed-term function-option-lst-syntax-p)
    :short "Recogizer for function-option-lst-syntax"
    (mbe :logic (if (function-option-lst-syntax-p term) term nil)
         :exec term))

  (defthm function-option-lst-syntax-fix-idempotent-lemma
    (equal (function-option-lst-syntax-fix (function-option-lst-syntax-fix x))
           (function-option-lst-syntax-fix x))
    :hints (("Goal" :in-theory (enable function-option-lst-syntax-fix))))

  (deffixtype function-option-lst-syntax
    :pred  function-option-lst-syntax-p
    :fix   function-option-lst-syntax-fix
    :equiv function-option-lst-syntax-equiv
    :define t
    :forward t
    :topic function-option-lst-syntax-p)

  (define function-syntax-p ((term t))
    :returns (syntax-good? booleanp)
    :short "Recognizer for function-syntax."
    (b* (((unless (true-listp term)) nil)
         ((unless (consp term)) t)
         ((cons fname function-options) term)
         (- (cw "(symbolp fname): ~q0" (symbolp fname)))
         (- (cw "(function-option-lst-syntax-p function-options): ~q0" (function-option-lst-syntax-p function-options))))
      ;; It's probably possible to check existence of function?
      ;; Currently not doing such check, since it will require passing state.
      (and (symbolp fname)
           (function-option-lst-syntax-p function-options))))

  (define function-syntax-fix ((term function-syntax-p))
    :returns (fixed-term function-syntax-p)
    :short "Fixing function for function-syntax-p"
    (mbe :logic (if (function-syntax-p term) term nil)
         :exec term))

  (defthm function-syntax-fix-idempotent-lemma
    (equal (function-syntax-fix (function-syntax-fix x))
           (function-syntax-fix x))
    :hints (("Goal" :in-theory (enable function-syntax-fix))))

  (deffixtype function-syntax
    :pred  function-syntax-p
    :fix   function-syntax-fix
    :equiv function-syntax-equiv
    :define t
    :forward t
    :topic function-syntax-p)

  (define function-lst-syntax-p ((term t))
    :returns (syntax-good? booleanp)
    :short "Recognizer for function-lst-syntax"
    (b* (((if (atom term)) (equal term nil))
         ((cons first rest) term))
      (and (function-syntax-p first)
           (function-lst-syntax-p rest))))

  (define function-lst-syntax-fix ((term function-lst-syntax-p))
    :returns (fixed-term function-lst-syntax-p
                         :hints (("Goal" :in-theory (enable
                                                     function-lst-syntax-p))))
    :short "Fixing function for function-lst-syntax-fix"
    :verify-guards nil
    (mbe :logic (if (consp term)
                    (cons (function-syntax-fix (car term))
                          (function-lst-syntax-fix (cdr term)))
                  nil)
         :exec term))
  (verify-guards function-lst-syntax-fix
    :hints (("Goal" :in-theory (enable function-lst-syntax-fix
                                       function-syntax-fix function-lst-syntax-p function-syntax-p))))

  (defthm function-lst-syntax-fix-idempotent-lemma
    (equal (function-lst-syntax-fix (function-lst-syntax-fix x))
           (function-lst-syntax-fix x))
    :hints (("Goal" :in-theory (enable function-lst-syntax-fix))))

  (deffixtype function-lst-syntax
    :pred  function-lst-syntax-p
    :fix   function-lst-syntax-fix
    :equiv function-lst-syntax-equiv
    :define t
    :forward t
    :topic function-lst-syntax-p)


  (define smt-solver-params-p ((term t))
    :returns (syntax-good? booleanp)
    :short "Recognizer for smt-solver-params."
    (true-listp term))

  (define smt-solver-params-fix ((term smt-solver-params-p))
    :returns (fixed-term smt-solver-params-p
                         :hints (("Goal" :in-theory (enable smt-solver-params-p))))
    :short "Fixing function for smt-solver-params."
    (mbe :logic (if (smt-solver-params-p term) term (true-list-fix term))
         :exec term))

  (defconst *cnf-options*
    '(:interface-dir :SMT-files-dir :SMT-module
                     :SMT-class :SMT-cmd :file-format))

  (define cnf-option-p ((option t))
    :returns (syntax-good? booleanp)
    :short "Recoginizer for cnf-option."
    (if (member-equal option *cnf-options*) t nil))

  (define cnf-option-fix ((option cnf-option-p))
    :returns (fixed-cnf-option cnf-option-p)
    :short "Fixing function for cnf-option."
    (mbe :logic (if (cnf-option-p option) option ':interface-dir)
         :exec option))

  (define cnf-option-lst-p ((option-lst t))
    :returns (syntax-good? booleanp)
    :short "Recoginizer for cnf-option-lst."
    (b* (((if (atom option-lst)) (equal option-lst nil))
         ((cons first rest) option-lst))
      (and (cnf-option-p first)
           (cnf-option-lst-p rest))))

  (define cnf-option-lst-fix ((option-lst cnf-option-lst-p))
    :returns (fixed-option-lst cnf-option-lst-p
                               :hints (("Goal" :in-theory (enable cnf-option-lst-p))))
    :short "Fixing function for cnf-option-lst."
    :verify-guards nil
    (mbe :logic (if (atom option-lst)
                    nil
                  (cons (cnf-option-fix (car option-lst))
                        (cnf-option-lst-fix (cdr option-lst))))
         :exec option-lst))
  (verify-guards cnf-option-lst-fix
    :hints (("Goal" :in-theory (enable cnf-option-fix
                                       cnf-option-lst-fix
                                       cnf-option-p cnf-option-lst-p))))


  (define smt-solver-single-cnf-p ((term t) (used cnf-option-lst-p))
    :returns (mv (syntax-good? booleanp)
                 (new-used cnf-option-lst-p
                           :hints (("Goal" :in-theory (enable cnf-option-lst-p cnf-option-p)))))
    :short "Recognizer for smt-solver-single-cnf."
    (b* ((used (cnf-option-lst-fix used))
         ((if (equal term nil)) (mv t used))
         ((unless (and (true-listp term) (car term)
                       (cadr term) (not (cddr term)))) (mv nil used))
         ((cons option body-lst) term)
         ((unless (cnf-option-p option)) (mv nil used)))
      (mv (and (not (member-equal option used))
               (stringp (car body-lst)))
          (cons option used))))

  (defthm member-equal-preserve
    (implies (not (member-equal x (cons a lst)))
             (not (member-equal x lst))))

  (define smt-solver-cnf-p-helper ((term t) (used cnf-option-lst-p))
    :returns (syntax-good? booleanp)
    :short "Helper function for smt-solver-cnf-p."
    (b* (((if (atom term)) (equal term nil))
         ((unless (and (true-listp term) (>= (len term) 2))) nil)
         ((list* first second rest) term)
         ((mv res new-used) (smt-solver-single-cnf-p (list first second) used)))
      (and res (smt-solver-cnf-p-helper rest new-used)))
    ///
    (defthm crock-true-listp
      (implies (smt-solver-cnf-p-helper term nil)
               (true-listp term)))

    (defthm stringp-of-cadr
      (implies (and (smt-solver-cnf-p-helper content nil)
                    (consp content))
               (stringp (cadr content)))
      :hints (("Goal"
               :in-theory (enable smt-solver-single-cnf-p))))

    (skip-proofs
     (defthm cddr-preserve
       (implies (and (smt-solver-cnf-p-helper content nil)
                     (consp content))
                (smt-solver-cnf-p-helper (cddr content)
                                         nil))
       :hints (("Goal"
                :in-theory (enable smt-solver-cnf-p-helper smt-solver-single-cnf-p member-equal)
                ;; :use ((:instance member-equal-preserve
                ;;                  (x )
                ;;                  (a )
                ;;                  (lst )))
                ))))
    )

  (define smt-solver-cnf-p ((term t))
    :returns (syntax-good? booleanp)
    :short "Recognizer for smt-solver-cnf."
    (smt-solver-cnf-p-helper term nil))

  (define smt-solver-cnf-fix ((term smt-solver-cnf-p))
    :returns (fixed-smt-cnf smt-solver-cnf-p)
    :short "Fixing function for smt-solver-cnf."
    (mbe :logic (if (smt-solver-cnf-p term) term nil)
         :exec term))

  (defthm smt-solver-cnf-fix-idempotent-lemma
    (equal (smt-solver-cnf-fix (smt-solver-cnf-fix x))
           (smt-solver-cnf-fix x))
    :hints (("Goal" :in-theory (enable smt-solver-cnf-fix))))

  (deffixtype smt-solver-cnf
    :pred  smt-solver-cnf-p
    :fix   smt-solver-cnf-fix
    :equiv smt-solver-cnf-equiv
    :define t
    :forward t
    :topic smt-solver-cnf-p)

  (defconst *smtlink-options*
    '((:functions . function-lst-syntax-p)
      (:hypotheses . hypothesis-lst-syntax-p)
      (:main-hint . hints-syntax-p)
      (:int-to-rat . booleanp)
      (:smt-fname . stringp)
      (:rm-file . booleanp)
      (:smt-solver-params . smt-solver-params-p)
      (:smt-solver-cnf . smt-solver-cnf-p)))

  (defconst *smtlink-option-names*
    (strip-cars *smtlink-options*))

  (defconst *smtlink-option-types*
    (remove-duplicates-equal (strip-cdrs *smtlink-options*)))

  (define smtlink-option-type-p ((option-type t))
    :returns (syntax-good? booleanp)
    :short "Recoginizer for smtlink-option-type."
    (if (member-equal option-type *smtlink-option-types*) t nil))

  (define smtlink-option-type-fix ((opttype smtlink-option-type-p))
    :returns (fixed-opttype smtlink-option-type-p
                            :hints (("Goal" :in-theory (enable
                                                        smtlink-option-type-p))))
    :short "Fixing function for smtlink-option-type."
    (mbe :logic (if (smtlink-option-type-p opttype) opttype 'function-lst-syntax-p)
         :exec opttype))

  (define smtlink-option-name-p ((option-name t))
    :returns (syntax-good? booleanp)
    :short "Recoginizer for an smtlink-option-name."
    (if (member-equal option-name *smtlink-option-names*) t nil))

  (define smtlink-option-name-fix ((option smtlink-option-name-p))
    :returns (fixed-smtlink-option-name smtlink-option-name-p)
    :short "Fixing function for smtlink-option-name."
    (mbe :logic (if (smtlink-option-name-p option) option ':functions)
         :exec option))

  (define smtlink-option-name-lst-p ((option-lst t))
    :returns (syntax-good? booleanp)
    :short "Recoginizer for smtlink-option-name-lst."
    (b* (((if (atom option-lst)) (equal option-lst nil))
         ((cons first rest) option-lst))
      (and (smtlink-option-name-p first)
           (smtlink-option-name-lst-p rest))))

  (define smtlink-option-name-lst-fix ((option-lst smtlink-option-name-lst-p))
    :returns (fixed-option-name-lst smtlink-option-name-lst-p
                                    :hints (("Goal" :in-theory (enable smtlink-option-name-lst-p))))
    :short "Fixing function for option-name-lst."
    :verify-guards nil
    (mbe :logic (if (atom option-lst)
                    nil
                  (cons (smtlink-option-name-fix (car option-lst))
                        (smtlink-option-name-lst-fix (cdr option-lst))))
         :exec option-lst))
  (verify-guards smtlink-option-name-lst-fix
    :hints (("Goal" :in-theory (enable smtlink-option-name-fix
                                       smtlink-option-name-lst-fix
                                       smtlink-option-name-p smtlink-option-name-lst-p))))

  (define eval-smtlink-option-type ((option-type smtlink-option-type-p) (term t))
    :returns (type-correct? booleanp)
    :short "Evaluating types for smtlink option body."
    (case option-type
      (function-lst-syntax-p (function-lst-syntax-p term))
      (hypothesis-lst-syntax-p (hypothesis-lst-syntax-p term))
      (hints-syntax-p (hints-syntax-p term))
      (booleanp (booleanp term))
      (stringp (stringp term))
      (smt-solver-params-p (smt-solver-params-p term))
      (t (smt-solver-cnf-p term))))

  (define smtlink-option-syntax-p ((term t) (used smtlink-option-name-lst-p))
    :returns (mv (syntax-good? booleanp)
                 (used? smtlink-option-name-lst-p
                        :hints (("Goal" :in-theory (enable smtlink-option-name-lst-p smtlink-option-name-p)))))
    :short "Recoginizer for smtlink-option-syntax."
    :verify-guards nil
    (b* ((used (smtlink-option-name-lst-fix used))
         ((if (equal term nil)) (mv t used))
         ((unless (and (true-listp term) (car term) (not (cddr term)))) (mv nil used))
         ((cons option body-lst) term)
         ((unless (smtlink-option-name-p option)) (mv nil used))
         (option-type (cdr (assoc-equal option *smtlink-options*)))
         (- (cw "option-type: ~q0" option-type))
         (- (cw "(eval-smtlink-option-type option-type (car body-lst)): ~q0" (eval-smtlink-option-type option-type (car body-lst)))))
      (mv (and (not (member-equal option used))
               (eval-smtlink-option-type option-type (car body-lst)))
          (cons option used))))
  (verify-guards smtlink-option-syntax-p
    :guard-debug t
    :hints (("Goal" :in-theory (enable smtlink-option-syntax-p smtlink-option-name-p
                                       eval-smtlink-option-type smtlink-option-name-lst-p))))

  (define smtlink-hint-syntax-p-helper ((term t) (used smtlink-option-name-lst-p))
    :returns (syntax-good? booleanp)
    :short "Helper function for smtlink-hint-syntax-p."
    (b* (((if (atom term)) (equal term nil))
         ((unless (and (true-listp term) (>= (len term) 2))) nil)
         ((list* first second rest) term)
         (- (cw "first: ~q0" first))
         (- (cw "second: ~q0" second))
         ((mv res new-used) (smtlink-option-syntax-p (list first second) used)))
      (and res (smtlink-hint-syntax-p-helper rest new-used)))
    ///
    (defthm function-lst-syntax-p-constraint
      (implies (and (smtlink-hint-syntax-p-helper user-hint nil)
                    (consp user-hint)
                    (consp (cdr user-hint)))
               (or (equal (car user-hint) ':functions)
                   (equal (car user-hint) ':hypotheses)
                   (equal (car user-hint) ':main-hint)
                   (equal (car user-hint) ':int-to-rat)
                   (equal (car user-hint) ':smt-fname)
                   (equal (car user-hint) ':rm-file)
                   (equal (car user-hint) ':smt-solver-params)
                   (equal (car user-hint) ':smt-solver-cnf)))
      :hints (("Goal"
               :in-theory (enable eval-smtlink-option-type
                                  smtlink-option-syntax-p
                                  smtlink-option-name-p))))

    (defthm function-lst-syntax-p-of-option
      (implies
       (and (consp (cdr user-hint))
            (smtlink-hint-syntax-p-helper user-hint nil)
            (consp user-hint))
       (and (implies (equal (car user-hint) ':functions)
                     (function-lst-syntax-p (cadr user-hint)))
            (implies (equal (car user-hint) ':hypotheses)
                     (hypothesis-lst-syntax-p (cadr user-hint)))
            (implies (equal (car user-hint) ':main-hint)
                     (hints-syntax-p (cadr user-hint)))
            (implies (equal (car user-hint) ':int-to-rat)
                     (booleanp (cadr user-hint)))
            (implies (equal (car user-hint) ':smt-fname)
                     (stringp (cadr user-hint)))
            (implies (equal (car user-hint) ':rm-file)
                     (booleanp (cadr user-hint)))
            (implies (equal (car user-hint) ':smt-solver-params)
                     (smt-solver-params-p (cadr user-hint)))
            (implies (equal (car user-hint) ':smt-solver-cnf)
                     (smt-solver-cnf-p (cadr user-hint)))))
      :hints (("Goal"
               :in-theory (enable smtlink-option-syntax-p
                                  eval-smtlink-option-type))))

    (skip-proofs
     (defthm smtlink-hint-syntax-preserve
       (implies (and (smtlink-hint-syntax-p-helper term nil)
                     (consp term))
                (smtlink-hint-syntax-p-helper (cddr term)
                                              nil))))
    )

  (define smtlink-hint-syntax-p ((term t))
    :returns (syntax-good? booleanp)
    :short "Recognizer for smtlink-hint-syntax."
    (smtlink-hint-syntax-p-helper term nil))

  ;; Strange fixing function.
  (define smtlink-hint-syntax-fix ((term smtlink-hint-syntax-p))
    :short "Fixing function for smtlink-hint-syntax."
    :returns (fixed-smtlink-hint-syntax smtlink-hint-syntax-p)
    (mbe :logic (if (smtlink-hint-syntax-p term) term nil)
         :exec term))

  ;; -------------------------------------------------------------------------
  ;; (local (in-theory (enable pseudo-termp)))

  ;; (defthm symbolp-is-pseudo-termp-crock
  ;;   (implies (symbolp x) (pseudo-termp x)))

  (define make-merge-formals-helper ((content argument-lst-syntax-p) (smt-func func-p))
    :returns (func func-p)
    :short "Adding user defined formals to overwrite what's already in smt-func."
    :measure (len content)
    :hints (("Goal" :in-theory (enable argument-lst-syntax-fix)))
    :verify-guards nil
    (b* ((content (argument-lst-syntax-fix content))
         (smt-func (func-fix smt-func))
         ((func f) smt-func)
         ((unless (consp content)) smt-func)
         ((cons first rest) content)
         ((list* argname type & hints) first)
         (new-formals (cons (make-decl :name argname
                                       :type (make-hint-pair :thm type
                                                             :hints hints))
                            f.formals))
         (new-func (change-func f :formals new-formals)))
      (make-merge-formals-helper rest new-func)))

  (verify-guards make-merge-formals-helper
    :hints (("Goal" :in-theory (enable argument-lst-syntax-fix
                                       argument-lst-syntax-p
                                       argument-syntax-fix
                                       argument-syntax-p
                                       smt-typep
                                       hints-syntax-p))))

  (define remove-duplicate-from-decl-list ((decls decl-listp) (seen symbol-listp))
    :returns (simple-decls decl-listp)
    :short "Remove shadowed decls from decl-list"
    :measure (len decls)
    (b* ((decls (decl-list-fix decls))
         ((unless (consp decls)) nil)
         ((cons first rest) decls)
         ((decl d) first)
         (seen? (member-equal d.name seen))
         ((if seen?) (remove-duplicate-from-decl-list rest seen)))
      (cons first (remove-duplicate-from-decl-list rest (cons d.name seen)))))

  (define make-merge-formals ((content argument-lst-syntax-p) (smt-func func-p))
    :returns (func func-p)
    :short "Adding user defined formals to overwrite what's already in smt-func."
    (b* ((new-func (make-merge-formals-helper content smt-func))
         ((func f) new-func))
      (change-func f :formals (remove-duplicate-from-decl-list f.formals nil))))

  (define make-merge-returns-helper ((content argument-lst-syntax-p) (smt-func func-p))
    :returns (func func-p)
    :short "Adding user defined returns to overwrite what's already in smt-func."
    :measure (len content)
    :hints (("Goal" :in-theory (enable argument-lst-syntax-fix)))
    :verify-guards nil
    (b* ((content (argument-lst-syntax-fix content))
         (smt-func (func-fix smt-func))
         ((func f) smt-func)
         ((unless (consp content)) smt-func)
         ((cons first rest) content)
         ((cons argname (cons type (cons & hints))) first)
         (new-returns (cons (make-decl :name argname
                                       :type (make-hint-pair :thm type
                                                             :hints hints))
                            f.returnss))
         (new-func (change-func f :returns new-returns)))
      (make-merge-returns-helper rest new-func)))

  (verify-guards make-merge-returns-helper
    :hints (("Goal" :in-theory (enable argument-lst-syntax-fix
                                       argument-lst-syntax-p
                                       argument-syntax-p
                                       argument-syntax-fix
                                       hints-syntax-p
                                       smt-typep
                                       ))))

  (define make-merge-returns ((content argument-lst-syntax-p) (smt-func func-p))
    :returns (func func-p)
    :short "Adding user defined returns to overwrite what's already in smt-func."
    (b* ((new-func (make-merge-returns-helper content smt-func))
         ((func f) new-func))
      (change-func f :returns (remove-duplicate-from-decl-list f.returns nil))))

  (define make-merge-guard ((content hypothesis-syntax-p) (smt-func func-p))
    :returns (func func-p)
    :short "Adding user defined guard to smt-func."
    :verify-guards nil
    (b* ((content (hypothesis-syntax-fix content))
         (smt-func (func-fix smt-func))
         ((cons thm (cons & hints-lst)) content)
         (hints (car hints-lst))
         (new-guard (make-hint-pair :thm thm :hints hints)))
      (change-func smt-func :guard new-guard)))

  (verify-guards make-merge-guard
    :hints (("Goal"
             :in-theory (enable hypothesis-syntax-fix hypothesis-syntax-p))))


  (define make-merge-more-returns ((content hypothesis-lst-syntax-p)
                                   (smt-func func-p))
    :returns (func func-p)
    :short "Adding user-defined more-return theorems."
    :measure (len content)
    :hints (("Goal" :in-theory (enable hypothesis-lst-syntax-fix)))
    :verify-guards nil
    (b* ((content (hypothesis-lst-syntax-fix content))
         (smt-func (func-fix smt-func))
         ((func f) smt-func)
         ((unless (consp content)) smt-func)
         ((cons first rest) content)
         ((cons thm (cons & hints-lst)) first)
         (hints (car hints-lst))
         (new-more-return (make-hint-pair :thm thm :hints hints))
         (new-func (change-func smt-func
                                :more-returns (cons new-more-return f.more-returns))))
      (make-merge-more-returns rest new-func)))

  (defthm cdr-of-hypothesis-lst-syntax-fix-crock
    (hypothesis-lst-syntax-p (cdr (hypothesis-lst-syntax-fix content)))
    :hints (("Goal"
             :in-theory (enable hypothesis-lst-syntax-fix))))

  (verify-guards make-merge-more-returns
    :guard-debug t
    :hints (("Goal" :in-theory (enable hypothesis-lst-syntax-p
                                       hypothesis-lst-syntax-fix
                                       hypothesis-syntax-p
                                       hypothesis-syntax-fix))))

  ;; BOZO:
  ;; This implementation is potentially slow because of the threading of smt-func
  ;; all the way while at the same time updating it.
  (define make-merge-function-option-lst ((fun-opt-lst function-option-lst-syntax-p)
                                          (smt-func func-p))
    :returns (func func-p)
    :short "Add option information into func."
    :measure (len fun-opt-lst)
    :hints (("Goal" :in-theory (enable function-option-lst-syntax-fix)))
    :verify-guards nil
    (b* ((fun-opt-lst (function-option-lst-syntax-fix fun-opt-lst))
         (smt-func (func-fix smt-func))
         ((unless (consp fun-opt-lst)) smt-func)
         ((cons option (cons content rest)) fun-opt-lst)
         (new-func (case option
                     (:formals (make-merge-formals content smt-func))
                     (:returns (make-merge-returns content smt-func))
                     (:level (change-func smt-func :expansion-depth content))
                     (:guard (make-merge-guard content smt-func))
                     (:more-returns (make-merge-more-returns content smt-func)))))
      (make-merge-function-option-lst rest new-func)))
(verify-guards make-merge-function-option-lst
  :hints (("Goal"
           :in-theory (e/d (function-option-lst-syntax-fix
                            function-option-lst-syntax-p
                            function-option-lst-syntax-p-helper
                            hypothesis-lst-syntax-p) (natp))
           :use ((:instance function-option-lst-syntax-p-of-option)
                 (:instance function-option-lst-syntax-p-constraint (any nil)))
           )))

  (define make-merge-function ((func function-syntax-p) (smt-func func-p))
    :returns (func func-p)
    :short "Function for generating func-p of a single function hint."
    :verify-guards nil
    (b* ((func (function-syntax-fix func))
         ((cons fun-name fun-opt-lst) func)
         (name fun-name))
      (make-merge-function-option-lst fun-opt-lst
                                      (change-func smt-func :name name))))
  (verify-guards make-merge-function
    :hints (("Goal" :in-theory (enable function-syntax-fix function-syntax-p))))

  (define merge-functions ((content function-lst-syntax-p) (hint smtlink-hint-p))
    :returns (new-hint smtlink-hint-p)
    :short "Merging function hints into smt-hint."
    :measure (len content)
    :hints (("Goal" :in-theory (enable function-lst-syntax-fix)))
    :verify-guards nil
    (b* ((hint (smtlink-hint-fix hint))
         (content (function-lst-syntax-fix content))
         ((unless (consp content)) hint)
         ((cons first rest) content)
         (name (car first))
         ((smtlink-hint h) hint)
         (exist? (hons-get name h.fast-functions))
         (smt-func (if exist? (cdr exist?) (make-func)))
         (new-func-lst (cons (make-merge-function first smt-func) h.functions))
         (new-hint (change-smtlink-hint hint :functions new-func-lst)))
      (merge-functions rest new-hint)))

  (verify-guards merge-functions
    :hints (("Goal" :in-theory (enable function-lst-syntax-fix
                                       function-lst-syntax-p
                                       function-syntax-p
                                       function-syntax-fix))))


  (define make-merge-hypothesis ((hypo hypothesis-syntax-p))
    :returns (hp hint-pair-p)
    :short "Generate a hint-pair for hypo"
    :verify-guards nil
    (b* ((hypo (hypothesis-syntax-fix hypo))
         ((list* thm & rest) hypo))
      (make-hint-pair :thm thm
                      :hints (car rest))))

  (verify-guards make-merge-hypothesis
    :guard-debug t
    :hints (("Goal" :in-theory (enable hypothesis-syntax-p hypothesis-syntax-fix hints-syntax-p))))

  (define merge-hypothesis ((content hypothesis-lst-syntax-p)
                            (hint smtlink-hint-p))
    :returns (new-hint smtlink-hint-p)
    :short "Merge hypothesis into hint"
    :measure (len content)
    :hints (("Goal" :in-theory (enable hypothesis-lst-syntax-fix)))
    :verify-guards nil
    (b* ((hint (smtlink-hint-fix hint))
         (content (hypothesis-lst-syntax-fix content))
         ((unless (consp content)) hint)
         ((cons first rest) content)
         ((smtlink-hint h) hint)
         (new-hypo-lst (cons (make-merge-hypothesis first) h.hypotheses))
         ;; It might be better to first generate the list of merging hypotheses
         ;; and then append the old lst after them. Not sure which one takes less
         ;; time, because I'm not sure about time complexity of
         ;; change-smtlink-hint. Append might be expensive, too.
         (new-hint (change-smtlink-hint hint :hypotheses new-hypo-lst)))
      (merge-hypothesis rest new-hint)))
  (verify-guards merge-hypothesis
    :hints (("Goal" :in-theory (enable hypothesis-lst-syntax-p hypothesis-lst-syntax-fix))))

  (define merge-main-hint ((content hints-syntax-p)
                           (hint smtlink-hint-p))
    :returns (new-hint smtlink-hint-p)
    :short "Merge main-hint"
    :verify-guards nil
    (b* ((hint (smtlink-hint-fix hint))
         (content (hints-syntax-fix content))
         (new-hint (change-smtlink-hint hint :main-hint content)))
      new-hint))
  (verify-guards merge-main-hint
    :hints (("Goal"
             :in-theory (enable hints-syntax-p))))

  (define set-int-to-rat ((content booleanp)
                          (hint smtlink-hint-p))
    :returns (new-hint smtlink-hint-p)
    :short "Set :int-to-rat based on user hint."
    (b* ((hint (smtlink-hint-fix hint))
         (new-hint (change-smtlink-hint hint :int-to-rat content)))
      new-hint))

  (define set-fname ((content stringp) (hint smtlink-hint-p))
    :returns (new-hint smtlink-hint-p)
    :short "Set :smt-fname."
    (b* ((hint (smtlink-hint-fix hint))
         (new-hint (change-smtlink-hint hint :smt-fname content)))
      new-hint))

  (define set-rm-file ((content booleanp)
                       (hint smtlink-hint-p))
    :returns (new-hint smtlink-hint-p)
    :short "Set :rm-file"
    (b* ((hint (smtlink-hint-fix hint))
         (new-hint (change-smtlink-hint hint :rm-file content)))
      new-hint))

  (define set-smt-solver-params ((content smt-solver-params-p)
                                 (hint smtlink-hint-p))
    :returns (new-hint smtlink-hint-p)
    :short "Set :smt-params"
    :verify-guards nil
    (b* ((hint (smtlink-hint-fix hint))
         (content (smt-solver-params-fix content))
         (new-hint (change-smtlink-hint hint :smt-params content)))
      new-hint))
  (verify-guards set-smt-solver-params
    :hints (("Goal"
             :in-theory (enable smt-solver-params-p smt-solver-params-fix))))

  (define merge-smt-solver-cnf ((content smt-solver-cnf-p)
                                (hint smtlink-hint-p))
    :returns (new-hint smtlink-hint-p)
    :short "Set :smt-cnf"
    :measure (len content)
    :hints (("Goal" :in-theory (enable smt-solver-cnf-fix)))
    :verify-guards nil
    (b* ((hint (smtlink-hint-fix hint))
         (content (smt-solver-cnf-fix content))
         ((unless (consp content)) hint)
         ((cons option (cons str rest)) content)
         ((smtlink-hint h) hint)
         (new-cnf (case option
                    (:interface-dir
                     (change-smtlink-config h.smt-cnf
                                            :interface-dir str))
                    (:SMT-files-dir
                     (change-smtlink-config h.smt-cnf
                                            :SMT-files-dir str))
                    (:SMT-module
                     (change-smtlink-config h.smt-cnf
                                            :SMT-module str))
                    (:SMT-class
                     (change-smtlink-config h.smt-cnf
                                            :SMT-class str))
                    (:SMT-cmd
                     (change-smtlink-config h.smt-cnf
                                            :SMT-cmd str))
                    (t
                     (change-smtlink-config h.smt-cnf
                                            :file-format str))))
         (new-hint (change-smtlink-hint hint :smt-cnf new-cnf)))
      (merge-smt-solver-cnf rest new-hint)))

  (verify-guards merge-smt-solver-cnf
    :guard-debug t
    :hints (("Goal" :in-theory (enable smt-solver-cnf-fix smt-solver-cnf-p
                                       smt-solver-cnf-p-helper)
             :use ((:instance stringp-of-cadr)))))

  (define combine-hints ((user-hint smtlink-hint-syntax-p) (hint smtlink-hint-p))
    :returns (combined-hint smtlink-hint-p)
    :hints (("Goal" :in-theory (enable smtlink-hint-syntax-fix)))
    :measure (len user-hint)
    :short "Combining user-hints into smt-hint."
    :verify-guards nil
    (b* ((hint (smtlink-hint-fix hint))
         (user-hint (smtlink-hint-syntax-fix user-hint))
         ((unless (consp user-hint)) hint)
         ((cons option (cons second rest)) user-hint)
         ((smtlink-hint h) hint)
         (fast-funcs (make-alist-fn-lst h.functions))
         (new-hint (case option
                     (:functions (with-fast-alist fast-funcs
                                   (merge-functions second
                                                    (change-smtlink-hint
                                                     hint
                                                     :fast-functions fast-funcs))))
                     (:hypotheses (merge-hypothesis second hint))
                     (:main-hint (merge-main-hint second hint))
                     (:int-to-rat (set-int-to-rat second hint))
                     (:smt-fname (set-fname second hint))
                     (:rm-file (set-rm-file second hint))
                     (:smt-solver-params (set-smt-solver-params second hint))
                     (t (merge-smt-solver-cnf second hint)))))
      (combine-hints rest new-hint)))

  (defthm true-listp-of-smtlink-hint-syntax-p
    (implies (smtlink-hint-syntax-p x)
             (true-listp x))
    :hints (("Goal" :in-theory (enable smtlink-hint-syntax-p
                                       smtlink-hint-syntax-p-helper))))
  (defthm crock
    (implies (and (true-listp x) (not (consp (cdr x)))) (not (cdr x))))

  (verify-guards combine-hints
    :guard-debug t
    :hints (("Goal"
             :in-theory (enable smtlink-hint-syntax-fix smtlink-hint-syntax-p smtlink-hint-syntax-p-helper)
             :use ((:instance true-listp-of-smtlink-hint-syntax-p (x user-hint))
                   (:instance crock (x user-hint))
                   (:instance function-lst-syntax-p-of-option)
                   (:instance function-lst-syntax-p-constraint)
                   (:instance smtlink-hint-syntax-preserve)))))

  (define process-hint ((cl pseudo-term-listp) (user-hint t))
    :returns (subgoal-lst pseudo-term-list-listp)
    (b* ((cl (pseudo-term-list-fix cl))
         (- (cw "user-hint: ~q0" user-hint))
         ((unless (smtlink-hint-syntax-p user-hint))
          (prog2$ (cw "User provided Smtlink hint can't be applied because of ~
    syntax error in the hints: ~q0Therefore proceed without Smtlink...~%" user-hint)
                  (list cl)))
         (combined-hint (combine-hints user-hint (smt-hint)))
         (- (cw "comined-hint: ~q0" combined-hint))
         (cp-hint `(:clause-processor (Smt-verified-cp clause ',combined-hint)))
         (subgoal-lst (cons `(hint-please ',cp-hint 'process-hint) cl)))
      (list subgoal-lst)))

  ;; ------------------------------------------------------------
  ;;         Prove correctness of clause processor
  ;;

  ;; -----------------------------------------------------------------
  ;;       Define evaluators

  (defevaluator ev-process-hint ev-lst-process-hint
    ((not x) (if x y z) (hint-please hint tag)))

  (def-join-thms ev-process-hint)

  (local (in-theory (enable process-hint)))
  (defthm correctness-of-process-hint
    (implies (and (pseudo-term-listp cl)
                  (alistp b)
                  (ev-process-hint
                   (conjoin-clauses (process-hint cl hint))
                   b))
             (ev-process-hint (disjoin cl) b))
    :rule-classes :clause-processor)

  ;; Smtlink is a macro that generates a clause processor hint. This clause
  ;;   processor hint generates a clause, with which a new smt-hint is attached.
  ;;   This new smt-hint combines user given hints with defattach hints.
  ;; A computed hint will be waiting to take the clause and hint for clause
  ;;   expansion and transformation.
  (defmacro Smtlink (clause hint)
    `(process-hint ,clause ,hint))
;;  )

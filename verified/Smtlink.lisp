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
;;                                          :more-returns ((> r0 0) :hints (:use ((:instance more-lemma))))))
;;                          :hypothesis (((> a b) :hints (:use ((:instance lemma)))))
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
       (equal (len term) 2)
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
       (equal (len term) 2)
       (equal (car term) 'quote)
       (natp (cadr term))))

(define qnat-fix ((term qnatp))
  :returns (fixed-term qnatp)
  :short "Fixing function for a qnatp."
  (mbe :logic (if (qnatp term) term ''0)
       :exec term))

(define qbooleanp ((term t))
  :short "Recognizer for a quoted booleanp."
  :returns (syntax-good? booleanp)
  (and (true-listp term)
       (equal (len term) 2)
       (equal (car term) 'quote)
       (booleanp (cadr term))))

(define qboolean-fix ((term qbooleanp))
  :returns (fixed-term qbooleanp)
  :short "Fixing function for a qbooleanp."
  (mbe :logic (if (qbooleanp term) term ''nil)
       :exec term))

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
           (equal (len term) 1)
           (pseudo-termp (car term)))
      ;; With hints
      (and (true-listp term)
           (equal (len term) 3)
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

(define hypothesis-lst-syntax-p ((term t))
  :returns (syntax-good? booleanp)
  :short "Recognizer for hypothesis-lst-syntax."
  (b* (((if (atom term)) (equal term nil))
       ((cons first rest) term))
    (and (hypothesis-syntax-p first)
         (hypothesis-lst-syntax-p rest))))

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
                    ' (rationalp realp rational/realp booleanp integerp))
      t nil))

(define argument-syntax-p ((term t))
  :returns (syntax-good? booleanp)
  :short "Recognizer for argument-syntax."
  (or (and (atom term)
           (equal term nil))
      ;; Just the name
      (and (true-listp term)
           (equal (len term) 1)
           (symbolp (car term)))
      ;; The name and the type/guard
      (and (true-listp term)
           (equal (len term) 2)
           (smt-typep (car term))
           (pseudo-termp (cadr term)))
      ;; The name, the type and the :hints
      (and (true-listp term)
           (equal (len term) 3)
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

(defconst *function-options*
  '((:formals . argument-lst-syntax-p)
    (:returns . argument-lst-syntax-p)
    (:level . qnatp)
    (:guard . hypothesis-lst-syntax-p)
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
  (mbe :logic (if (function-option-type-p option-type) option-type 'qnatp)
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

(define function-option-name-lst-p ((option-lst t))
  :returns (syntax-good? booleanp)
  :short "Recoginizer for option-lst."
  (b* (((if (atom option-lst)) (equal option-lst nil))
       ((cons first rest) option-lst))
    (and (function-option-name-p first)
         (function-option-name-lst-p rest))))

(define function-option-name-lst-fix ((option-lst function-option-name-lst-p))
  :returns (fixed-option-lst function-option-name-lst-p
                             :hints (("Goal" :in-theory (enable function-option-name-lst-p))))
  :short "Fixing function for option-name-lst."
  :verify-guards nil
  (mbe :logic (if (atom option-lst)
                  nil
                (cons (function-option-name-fix (car option-lst))
                      (function-option-name-lst-fix (cdr option-lst))))
       :exec option-lst))
(verify-guards function-option-name-lst-fix
  :hints (("Goal" :in-theory (enable function-option-name-fix
                                     function-option-name-lst-fix
                                     function-option-name-p function-option-name-lst-p))))

;; The conditions in eval-type should go along with *function-options*
(define eval-function-option-type ((option-type function-option-type-p) (term t))
  :returns (type-correct? booleanp)
  :short "Evaluating types for function option body."
  (b* ((option-type (function-option-type-fix option-type)))
    (case option-type
      (argument-lst-syntax-p (argument-lst-syntax-p term))
      (qnatp (qnatp term))
      (t (hypothesis-lst-syntax-p term)))))

(define function-option-syntax-p ((term t) (used function-option-name-lst-p))
  :returns (mv (syntax-good? booleanp)
               (used? function-option-name-lst-p
                      :hints (("Goal" :in-theory (enable function-option-name-lst-p function-option-name-p)))))
  :short "Recoginizer for function-option-syntax."
  :verify-guards nil
  (b* ((used (function-option-name-lst-fix used))
       ((if (equal term nil)) (mv t used))
       ((unless (and (true-listp term) (equal (len term) 2))) (mv nil used))
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

(define function-option-lst-syntax-p-helper ((term t) (used function-option-name-lst-p))
  :returns (syntax-good? booleanp)
  :short "Helper for function-option-lst-syntax-p."
  (b* (((if (atom term)) (equal term nil))
       ((unless (and (true-listp term) (>= (len term) 2))) nil)
       ((list* first second rest) term)
       ((mv res new-used) (function-option-syntax-p (list first second) used)))
    (and res (function-option-lst-syntax-p-helper rest new-used)))
  ///
  (skip-proofs
  (defthm function-option-lst-syntax-preserve
    (implies (and (function-option-lst-syntax-p-helper term nil)
                  (consp term))
             (function-option-lst-syntax-p-helper (cddr term)
                                                  nil))))

  (defthm function-option-lst-syntax-p-constraint
    (implies (and (function-option-lst-syntax-p-helper fun-opt-lst nil)
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
                   (qnatp (cadr fun-opt-lst)))
          (implies (equal (car fun-opt-lst) ':guard)
                   (hypothesis-lst-syntax-p (cadr fun-opt-lst)))
          (implies (equal (car fun-opt-lst) ':more-returns)
                   (hypothesis-lst-syntax-p (cadr fun-opt-lst)))))
    :hints (("Goal"
             :in-theory (enable function-option-syntax-p
                                eval-function-option-type))))
  )

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
       ((cons fname function-options) term))
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
       ((unless (and (true-listp term) (equal (len term) 2))) (mv nil used))
       ((cons option body-lst) term)
       ((unless (cnf-option-p option)) (mv nil used)))
    (mv (and (not (member-equal option used))
             (qstringp (car body-lst)))
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
             (stringp (cadadr content)))
    :hints (("Goal"
             :in-theory (enable smt-solver-single-cnf-p cnf-option-p
                                qstringp))))
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
    (:hypothesis . hypothesis-lst-syntax-p)
    (:main-hint . hints-syntax-p)
    (:int-to-rat . qbooleanp)
    (:smt-fname . qstringp)
    (:rm-file . qbooleanp)
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
    (qbooleanp (qbooleanp term))
    (qstringp (qstringp term))
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
       ((unless (and (true-listp term) (equal (len term) 2))) (mv nil used))
       ((cons option body-lst) term)
       ((unless (smtlink-option-name-p option)) (mv nil used))
       (option-type (cdr (assoc-equal option *smtlink-options*))))
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
       ((mv res new-used) (smtlink-option-syntax-p (list first second) used)))
    (and res (smtlink-hint-syntax-p-helper rest new-used)))
  ///
  (defthm function-lst-syntax-p-constraint
    (implies (and (smtlink-hint-syntax-p-helper user-hint nil)
                  (consp user-hint)
                  (consp (cdr user-hint)))
             (or (equal (car user-hint) ':functions)
                 (equal (car user-hint) ':hypothesis)
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
          (implies (equal (car user-hint) ':hypothesis)
                   (hypothesis-lst-syntax-p (cadr user-hint)))
          (implies (equal (car user-hint) ':main-hint)
                   (hints-syntax-p (cadr user-hint)))
          (implies (equal (car user-hint) ':int-to-rat)
                   (qbooleanp (cadr user-hint)))
          (implies (equal (car user-hint) ':smt-fname)
                   (qstringp (cadr user-hint)))
          (implies (equal (car user-hint) ':rm-file)
                   (qbooleanp (cadr user-hint)))
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

;; (stop)
(define make-merge-formals ((content argument-lst-syntax-p) (smt-func func-p))
  :returns (func func-p)
  :short "Adding user defined formals to overwrite what's already in smt-func."
  :ignore-ok t
  :irrelevant-formals-ok t
  (make-func))

(define make-merge-returns ((content argument-lst-syntax-p) (smf-func func-p))
  :returns (func func-p)
  :short "Adding user defined returns to overwrite what's already in smt-func."
  :ignore-ok t
  :irrelevant-formals-ok t
  (make-func))

(define make-merge-guard ((content hypothesis-lst-syntax-p) (smt-func func-p))
  :returns (func func-p)
  :short "Adding user defined guard to smt-func."
  :ignore-ok t
  :irrelevant-formals-ok t
  (make-func))

(define make-merge-more-returns ((content hypothesis-lst-syntax-p)
                                 (smt-func func-p))
  :returns (func func-p)
  :short "Adding user-defined more-return theorems."
  :ignore-ok t
  :irrelevant-formals-ok t
  (make-func))

(define make-merge-function-option-lst ((fun-opt-lst function-option-lst-syntax-p)
                                        (smt-fun func-p))
  :returns (func func-p)
  :short "Add option information into func."
  :measure (len fun-opt-lst)
  :hints (("Goal" :in-theory (enable function-option-lst-syntax-fix)))
  :verify-guards nil
  (b* ((fun-opt-lst (function-option-lst-syntax-fix fun-opt-lst))
       (smt-fun (func-fix smt-fun))
       ((unless (consp fun-opt-lst)) smt-fun)
       ((cons option (cons content rest)) fun-opt-lst)
       (new-func (case option
                   (:formals (make-merge-formals content smt-fun))
                   (:returns (make-merge-returns content smt-fun))
                   (:level (change-func smt-fun :expansion-depth (cadr content)))
                   (:guard (make-merge-guard content smt-fun))
                   (:more-returns (make-merge-more-returns content smt-fun)))))
    (make-merge-function-option-lst rest new-func)))
(verify-guards make-merge-function-option-lst
  :hints (("Goal"
           :in-theory (enable function-option-lst-syntax-fix
                              function-option-lst-syntax-p
                              function-option-lst-syntax-p-helper
                              qnatp)
           :use ((:instance function-option-lst-syntax-p-of-option)
                 (:instance function-option-lst-syntax-p-constraint))))) 

(define make-merge-function ((func function-syntax-p) (smt-fun func-p))
  :returns (func func-p)
  :short "Function for generating func-p of a single function hint."
  :verify-guards nil
  (b* ((func (function-syntax-fix func))
       ((cons fun-name fun-opt-lst) func)
       (name fun-name))
    (make-merge-function-option-lst fun-opt-lst
                                    (change-func smt-fun :name name))))
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
       (smt-fun (if exist? (cdr exist?) (make-func)))
       (new-func-lst (cons (make-merge-function first smt-fun) h.functions))
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
       ((cons thm (cons & rest)) hypo))
    (make-hint-pair :thm thm
                    :hints (car rest))))
(verify-guards make-merge-hypothesis
  :guard-debug t
  :hints (("Goal" :in-theory (enable hypothesis-syntax-p hypothesis-syntax-fix))))

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

(define set-int-to-rat ((content qbooleanp)
                        (hint smtlink-hint-p))
  :returns (new-hint smtlink-hint-p)
  :short "Set :int-to-rat based on user hint."
  :verify-guards nil
  (b* ((hint (smtlink-hint-fix hint))
       (content (qboolean-fix content))
       (new-hint (change-smtlink-hint hint :int-to-rat (cadr content))))
    new-hint))

(verify-guards set-int-to-rat
  :hints (("Goal"
           :in-theory (enable qbooleanp qboolean-fix))))

(define set-fname ((content qstringp) (hint smtlink-hint-p))
  :returns (new-hint smtlink-hint-p)
  :short "Set :smt-fname."
  :verify-guards nil
  (b* ((hint (smtlink-hint-fix hint))
       (content (qstring-fix content))
       (new-hint (change-smtlink-hint hint :smt-fname (cadr content))))
    new-hint))
(verify-guards set-fname
  :hints (("Goal"
           :in-theory (enable qstringp qstring-fix))))

(define set-rm-file ((content qbooleanp)
                     (hint smtlink-hint-p))
  :returns (new-hint smtlink-hint-p)
  :short "Set :rm-file"
  :verify-guards nil
  (b* ((hint (smtlink-hint-fix hint))
       (content (qboolean-fix content))
       (new-hint (change-smtlink-hint hint :rm-file (cadr content))))
    new-hint))
(verify-guards set-rm-file
  :hints (("Goal"
           :in-theory (enable qbooleanp qboolean-fix))))

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
                                          :interface-dir (cadr str)))
                  (:SMT-files-dir
                   (change-smtlink-config h.smt-cnf
                                          :SMT-files-dir (cadr str)))
                  (:SMT-module
                   (change-smtlink-config h.smt-cnf
                                          :SMT-module (cadr str)))
                  (:SMT-class
                   (change-smtlink-config h.smt-cnf
                                          :SMT-class (cadr str)))
                  (:SMT-cmd
                   (change-smtlink-config h.smt-cnf
                                          :SMT-cmd (cadr str)))
                  (t
                   (change-smtlink-config h.smt-cnf
                                          :file-format (cadr str)))))
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
                   (:hypothesis (merge-hypothesis second hint))
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
    :enabled t
    (b* ((cl (pseudo-term-list-fix cl))
         (- (cw "user-hint: ~q0" user-hint))
         ((unless (smtlink-hint-syntax-p user-hint))
          (prog2$ (cw "User provided Smtlink hint can't be applied because of
    syntax error in the hints: ~q0Therefore proceed with out Smtlink..." user-hint)
                  (list cl)))
         (combined-hint (combine-hints user-hint (smt-hint)))
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

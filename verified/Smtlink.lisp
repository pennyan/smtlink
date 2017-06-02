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
;;                          :smt-cnf ()))))
;;
;; Types:
;; qbooleanp/error
;; qnatp/error
;; qstringp/error
;; hints-syntax-p/error
;; hypothesis-syntax-p/error
;; hypothesis-lst-syntax-p/error
;; argument-syntax-p/error
;; argument-lst-syntax-p/error
;; function-option-syntax-p/error
;; function-option-lst-syntax-p/error
;; function-syntax-p/error
;; function-lst-syntax-p/error
;; smtlink-cnf-p/error
;; smt-solver-params-p/error
;; smtlink-hint-syntax-p/error

(define true-list-fix ((lst t))
  :short "Fixing function for true-listp."
  :returns (fixed-lst true-listp)
  (if (true-listp lst)
      lst
    nil))

(define qstringp ((term t))
  :returns (syntax-good? booleanp)
  :short "Recognizer for a quoted stringp."
  (and (true-listp term)
       (equal (len term) 2)
       (equal (car term) 'quote)
       (stringp (cadr term))))

(define qstring-fix ((term qstringp))
  :short "Fixing function for a qstringp."
  :returns (fixed-qstring qstringp)
  (mbe :logic (if (qstringp term) term ''"")
       :exec term))

(define qnatp ((term t))
  :returns (syntax-good? booleanp)
  :short "Recognizer for a quoted qnatp."
  (and (true-listp term)
       (equal (len term) 2)
       (equal (car term) 'quote)
       (natp (cadr term))))

(define qnat-fix ((term qnatp))
  :returns (fixed-qnat qnatp)
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
  :returns (fixed-qboolean qbooleanp)
  :short "Fixing function for a qbooleanp."
  (mbe :logic (if (qbooleanp term) term ''nil)
       :exec term))

(define hints-syntax-p ((term t))
  :returns (syntax-good? booleanp)
  :short "Recognizer for hints-syntax."
  (true-listp term))

(define hints-syntax-fix ((term hints-syntax-p))
  :returns (fixed-hints-syntax hints-syntax-p)
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
           (hints-syntax-p (caddr term)))))

(define hypothesis-syntax-fix ((term hypothesis-syntax-p))
  :returns (fixed-hypothesis hypothesis-syntax-p)
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
  :returns (fixed-hypothesis-lst-syntax hypothesis-lst-syntax-p
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
  :returns (fixed-argument-syntax argument-syntax-p)
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
  :returns (fixed-argument-lst-syntax argument-lst-syntax-p
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

(defconst *function-option*
  '((:formals . argument-lst-syntax-p)
    (:returns . argument-lst-syntax-p)
    (:level . qnatp)
    (:guard . hypothesis-lst-syntax-p)
    (:more-returns . hypothesis-lst-syntax-p)))

(defconst *option-type*
  (strip-cdrs *function-option*))

(define function-option-p ((term t))
  :returns (syntax-good? booleanp)
  :short "Recoginizer for function-option."
  (if (assoc-equal term *function-option*) t nil))

(define option-type-p ((option t))
  :returns (syntax-good? booleanp)
  :short "Recoginizer for option-type."
  (if (member-equal option *option-type*) t nil))

(define option-type-lst-p ((option-lst t))
  :returns (syntax-good? booleanp)
  :short "Recoginizer for option-type-lst."
  (b* (((if (atom option-lst)) (equal option-lst nil))
       ((cons first rest) option-lst))
    (and (option-type-p first)
         (option-type-lst-p rest))))

;; The conditions in eval-type should go along with *function-option*
(define eval-type ((option-type option-type-p) (term t))
  :returns (type-cuorrect? booleanp)
  :short "Evaluating types for function option body."
  (case option-type
    (:formals (argument-lst-syntax-p term))
    (:returns (argument-lst-syntax-p term))
    (:level (qnatp term))
    (:guard (hypothesis-lst-syntax-p term))
    (t (hypothesis-lst-syntax-p term))))

(define function-option-syntax-p ((term t) (used option-type-lst-p))
  :returns (syntax-good? booleanp)
  :short "Recoginizer for function-option-syntax."
  :verify-guards nil
  (b* (((if (equal term nil)) t)
       ((unless (and (true-listp term) (equal (len term) 2))) nil)
       ((cons option body-lst) term)
       ((unless (function-option-p option)) nil)
       (option-type (cdr (assoc-equal option *function-option*))))
    (and (not (member-equal option used))
         (eval-type option-type (car body-lst)))))
(verify-guards function-option-syntax-p
  :guard-debug t
  :hints (("Goal" :in-theory (enable function-option-syntax-p function-option-p
                                     eval-type option-type-lst-p))))

(define function-option-syntax-fix ((term function-option-syntax-p) (used option-type-lst-p))
  :returns (fixed-function-option-syntax function-option-syntax-p)
  :short "Fixing function for function-option-syntax."
  (mbe :logic (if (function-option-syntax-p term used) term nil)
       :exec term))

(define function-option-lst-syntax-p (())
  :returns ())
(define function-option-lst-syntax-fix ())

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
  :returns (fixed-function-syntax function-syntax-p)
  :short "Fixing function for function-syntax."
  ())

(define function-lst-syntax-fix)
(define function-lst-syntax-p)

(define smtlink-hint-syntax-fix)
(define smtlink-hint-syntax-p)

(defconst *func-specs-syntax-lst*
  '((:formals . p)
    (:returns . p)
    (:level . qnatp)
    (:guard . p)
    (:more-returns . p)))

  (define eval-type ((type symbolp) (content t))
    :short "Evaluate if a content is of the given type."
    :returns (type-correct? booleanp)
    (cond ((equal type 'booleanp) (booleanp content))
          ((equal type 'stringp) (stringp content))
          ((equal type 'true-listp) (true-listp content))
          ((equal type 'natp) (natp content))
          ((equal type 'smtlink-config-p) (smtlink-config-p content))
          (t (symbolp content))))

(define hint-pair-syntax-p ((hint-pair t))
  :returns (syntax-good? booleanp)
  (or (and (equal (len hint-pair) 3) (symbolp (car hint-pair))
           (equal (cadr hint-pair) ':hints) (listp (caddr hint-pair)))
      (and (equal (len hint-pair) 1) (symbolp (car hint-pair)))))

  (define save-hint-pair-list ((hypo-lst true-listp))
    :returns (saved-hypo-lst hint-pair-listp)
    :measure (len hypo-lst)
    :hints (("Goal" :in-theory (enable true-list-fix)))
    :verify-guards nil
    (b* ((hypo-lst (true-list-fix hypo-lst))
         ((unless (consp hypo-lst)) nil)
         ((cons first rest) hypo-lst)
         ((unless (hint-pair-syntax-p first))
          (er hard? 'Smtlink=>save-hint-pair-list "Wrong format of Smtlink-hint
  hint-pair: ~q0" first))
         ((cons thm hints) first))
      (cons (case-match
              hints
              ((':hints hints) (make-hint-pair :thm thm :hints hints))
              (& (make-hint-pair :thm thm)))
            (save-hint-pair-list rest))))

(verify-guards save-hint-pair-list
  :hints (("Goal" :in-theory (enable hint-pair-syntax-p))))

  (define decl-syntax-p ((decl t))
    :returns (syntax-good? booleanp)
    (or (and (equal (len decl) 4) (symbolp (car decl))
             (hint-pair-syntax-p (cdr decl)))
        (and (equal (len decl) 2) (symbolp (car decl))
             (hint-pair-syntax-p (cdr decl)))))

;; This function requires supper long proof.
(define save-decl-list ((decl-lst true-listp))
  :returns (saved-decl-lst decl-listp)
  :measure (len decl-lst)
  :hints (("Goal" :in-theory (enable true-list-fix)))
  :verify-guards nil
  (b* ((decl-lst (true-list-fix decl-lst))
       ((unless (consp decl-lst)) nil)
       ((cons first rest) decl-lst)
       ((unless (decl-syntax-p first))
        (er hard? 'Smtlink=>save-decl-list "Wrong format of Smtlink-hint decl:
  ~q0" first))
       ((cons name (cons type hint-pair)) first)
       (hint-pair (case-match
                    hint-pair
                    ((':hints hints) (make-hint-pair :thm type :hints hints))
                    (& (make-hint-pair :thm type)))))
    (cons (make-decl :name name :type hint-pair)
          (save-decl-list rest))))

(verify-guards save-decl-list
  :hints (("Goal" :in-theory (enable decl-syntax-p hint-pair-syntax-p))))


(define check-func-specs-syntax ((func-spec-lst true-listp) (used true-listp))
  :returns (syntax-good? booleanp)
  :hints (("Goal" :in-theory (enable true-list-fix)))
  (b* ((func-spec-lst (true-list-fix func-spec-lst))
       (used (true-list-fix used))
       ((if (endp func-spec-lst)) t)
       ((unless (and (car func-spec-lst) (cadr func-spec-lst))) nil)
       ((cons first rest) func-spec-lst)
       ((cons second rest-of-second) rest)
       ((if (member-equal first used))
        (er hard? 'Smtlink=>check-func-specs-syntax "Already defined ~p0.~%" first))
       (exist? (assoc-equal first *func-specs-syntax-lst*))
       ((unless exist?) nil)
       (type (cdr exist?))
       (type-correct? (eval-type type second))
       ((unless type-correct?) nil))
    (check-func-specs-syntax rest-of-second (cons first used)))
  ///
  (skip-proofs
   (defthm test
     (IMPLIES (AND (CHECK-FUNC-SPECS-SYNTAX OTHER NIL))
              (CHECK-FUNC-SPECS-SYNTAX (CDDR OTHER) NIL))))

  (defthm check-func-specs-syntax-natp
    (implies (and (true-listp other)
                  (check-func-specs-syntax other nil)
                  (equal (car other) :level))
             (natp (cadr other)))
    :hints (("Goal" :in-theory (enable true-list-fix eval-type))))

  (defthm check-func-specs-syntax-true-listp
    (implies (and (true-listp other)
                  (check-func-specs-syntax other nil)
                  (or (equal (car other) :formals)
                      (equal (car other) :more-returns)
                      (equal (car other) :guard)
                      (equal (car other) :returns)))
             (true-listp (cadr other)))
    :hints (("Goal" :in-theory (enable true-list-fix eval-type))))
  )

(define func-specs-syntax-p ((func-specs t))
  :returns (syntax-good? booleanp)
  (b* (((unless (true-listp func-specs)) nil)
       ((unless (<= (len func-specs) 10)) nil))
    (check-func-specs-syntax func-specs nil)))

(define func-specs-syntax-fix ((func-specs func-specs-syntax-p))
  :returns (fixed-func-specs func-specs-syntax-p)
  (if (func-specs-syntax-p func-specs) func-specs nil))

(define save-a-function ((name symbolp) (other func-specs-syntax-p) (func func-p))
  :returns (saved-func func-p)
  :measure (len other)
  :verify-guards nil
  :hints (("Goal" :in-theory (enable func-specs-syntax-fix)))
  (b* ((name (symbol-fix name))
       (other (func-specs-syntax-fix other))
       ((unless (consp other)) (make-func))
       ((cons first rest) other)
       ((cons second rest-of-second) rest))
    (case first
      (:formals
       (save-a-function name rest-of-second
                        (change-func func :formals (save-decl-list second))))
      (:guard
       (save-a-function name rest-of-second
                        (change-func func :guard (save-hint-pair-list second))))
      (:returns
       (save-a-function name rest-of-second
                        (change-func func :returns (save-decl-list second))))
      (:more-returns
       (save-a-function name rest-of-second
                        (change-func func :more-returns (save-hint-pair-list second))))
      (:level
       (save-a-function name rest-of-second
                        (change-func func :expansion-depth second)))
      (t (prog2$
          (er hard? 'Smtlink=>save-a-function "Functions hint in Smtlink hint
  seems in the wrong format ~p0.~%" other)
          (make-func))))))

(verify-guards save-a-function
  :hints (("Goal" :in-theory (enable func-specs-syntax-fix func-specs-syntax-p
  eval-type assoc-equal check-func-specs-syntax)))
  :guard-debug t)

(define func-syntax-p ((func t))
  :returns (syntax-good? booleanp)
  (and (true-listp func)
       (symbolp (car func))
       (func-specs-syntax-p (cdr func))))

(define save-functions ((func-lst true-listp))
  :returns (saved-funcs func-alistp
                        :hints (("Goal" :in-theory (enable true-list-fix func-syntax-p))))
  :measure (len func-lst)
  :hints (("Goal" :in-theory (enable true-list-fix)))
  :verify-guards nil
  (b* ((func-lst (true-list-fix func-lst))
       ((unless (consp func-lst)) nil)
       ((cons first rest) func-lst)
       ((unless (func-syntax-p first))
        (prog2$
         (er hard? 'Smtlink=>save-functions "Wrong syntax for Smtlink function
  declaration ~q0" first)
         nil))
       ((cons name other) first)
       (saved-func (save-a-function name other (make-func))))
    (cons (cons name saved-func)
          (save-functions rest))))

(verify-guards save-functions
  :guard-debug t
  :hints (("Goal" :in-theory (enable func-syntax-p))))


  (define check-syntax ((hint-lst true-listp) (used true-listp))
    :short "Main function for checking the syntax of a Smtlink hint list."
    :returns (syntax-good? booleanp)
    :hints (("Goal" :in-theory (enable true-list-fix)))
    (b* ((hint-lst (true-list-fix hint-lst))
         ((unless (consp hint-lst)) t)
         ((cons kwd rest) hint-lst)
         ((unless (consp rest)) (er hard? 'Smtlink=>check-syntax "wrong syntax ~p0.~%" hint-lst))
         ((cons second rest-of-second) rest)
         ((if (member-equal kwd used))
          (er hard? 'Smtlink=>check-syntax "Already defined ~p0.~%" kwd))
         (exist? (assoc-equal kwd *syntax-lst*))
         ((unless exist?) (er hard? 'Smtlink=>check-syntax "unrecognized keyword ~p0.~%" kwd))
         ;; (type (cdr exist?))
         ;; (type-correct? (eval-type type second))
         ;; ((unless type-correct?) nil)
         )
      (check-syntax rest-of-second (cons first used)))
    ///
    (defthm check-syntax-cddr-lemma
      (implies (check-syntax user-hints lst)
               (check-syntax user-hints nil))
      :hints (("Goal"
               :in-theory (enable true-list-fix)
               :cases (member-euqla first used)
               )))

    (defthm check-syntax-cddr
      (implies (check-syntax user-hints nil)
               (check-syntax (cddr user-hints) nil))
      :hints (("Goal" :in-theory (enable true-list-fix))))

    (defthm check-syntax-true-listp
      (implies (and (true-listp hint-lst)
                    (check-syntax hint-lst nil)
                    (or (equal (car hint-lst) :functions)
                        (equal (car hint-lst) :hypotheses)
                        (equal (car hint-lst) :main-hint)
                        (equal (car hint-lst) :smt-solver-params)))
               (true-listp (cadr hint-lst)))
      :hints (("Goal" :in-theory (enable true-list-fix eval-type))))

    (defthm check-syntax-smtlink-config-p
      (implies (and (true-listp hint-lst)
                    (check-syntax hint-lst nil)
                    (equal (car hint-lst) :smt-cnf))
               (smtlink-config-p (cadr hint-lst)))
      :hints (("Goal" :in-theory (enable true-list-fix eval-type))))

    (defthm check-syntax-booleanp
      (implies (and (true-listp hint-lst)
                    (check-syntax hint-lst nil)
                    (or (equal (car hint-lst) :int-to-rat)
                        (equal (car hint-lst) :rm-file)))
               (booleanp (cadr hint-lst)))
      :hints (("Goal" :in-theory (enable true-list-fix eval-type))))

    (defthm check-syntax-stringp
      (implies (and (true-listp hint-lst)
                    (check-syntax hint-lst nil)
                    (equal (car hint-lst) :smt-fname))
               (stringp (cadr hint-lst)))
      :hints (("Goal" :in-theory (enable true-list-fix eval-type))))
    )

  (define smtlink-hint-syntax-p ((hint-lst t))
    :short "Syntax check for Smtlink hint."
    :returns (syntax-good? booleanp)
    (b* (;; hint-lst should be a listp
         ((unless (true-listp hint-lst)) nil)
         ;; hint-lst should not exceed a length of 16 elements
         ((unless (<= (len hint-lst) 16)) nil))
      (check-syntax hint-lst nil)))

  (define smtlink-hint-syntax-fix ((hint-lst smtlink-hint-syntax-p))
    :short "Fixing function for Smtlink hint syntax."
    :returns (fixed-syntax smtlink-hint-syntax-p)
    :ignore-ok t
    :irrelevant-formals-ok t
    (if (smtlink-hint-syntax-p hint-lst) hint-lst nil))

(define save-user-hints ((user-hints smtlink-hint-syntax-p) (the-hint smtlink-hint-p))
  :returns (structured-hint maybe-smtlink-hint-p)
  :measure (len user-hints)
  :hints (("Goal" :in-theory (enable smtlink-hint-syntax-fix)))
  :verify-guards nil
  (b* ((user-hints (smtlink-hint-syntax-fix user-hints))
       ((unless (consp user-hints)) nil)
       (the-hint (smtlink-hint-fix the-hint))
       ((cons first rest) user-hints)
       ((cons second rest-of-second) rest))
    (case first
      (:functions
       (save-user-hints rest-of-second
                        (change-smtlink-hint the-hint :user-functions (save-functions second))))
      (:hypotheses
       (save-user-hints rest-of-second
                        (change-smtlink-hint the-hint :hypotheses (save-hint-pair-list second))))
      (:main-hint
       (save-user-hints rest-of-second
                        (change-smtlink-hint the-hint :main-hint second)))
      (:int-to-rat
       (save-user-hints rest-of-second
                        (change-smtlink-hint the-hint :int-to-rat second)))
      (:smt-fname
       (save-user-hints rest-of-second
                        (change-smtlink-hint the-hint :smt-fname second)))
      (:rm-file
       (save-user-hints rest-of-second
                        (change-smtlink-hint the-hint :rm-file second)))
      (:smt-solver-params
       (save-user-hints rest-of-second
                        (change-smtlink-hint the-hint :smt-params second)))
      (:smt-cnf
       (save-user-hints rest-of-second
                        (change-smtlink-hint the-hint :smt-cnf second)))
      ;; :smt-cnf
      ;; There might be problems with the merge of smt-cnf.
      ;; I'm assuming smt-cnf is already in its correct form.
      (t (er hard? 'Smtlink=>save-user-hints "Smtlink hint seems in the wrong format ~p0.~%" user-hints)))))

(verify-guards save-user-hints
  :guard-debug t
  :hints (("Goal"
           :in-theory (enable smtlink-hint-syntax-fix
                              smtlink-hint-syntax-p check-syntax)
           :use ((:instance check-syntax-true-listp)))))

(define merge-decl-list ((added-decls decl-listp) (master-adecls decl-alistp))
  :returns (merged-decl-list decl-alistp)
  :measure (len added-decls)
  (b* ((added-decls (decl-list-fix added-decls))
       (master-adecls (decl-alist-fix master-adecls))
       ((unless (consp added-decls)) master-adecls)
       ((cons first rest) added-decls)
       ((decl d) first))
    (merge-decl-list rest (hons-acons d.name first master-adecls))))

(define merge-a-function ((fn func-p) (mfn func-p))
  :returns (merged-fn func-p)
  :verify-guards nil
  (b* ((fn (func-fix fn))
       (mfn (func-fix mfn))
       ((func f) fn)
       ((func mf) mfn)
       ((unless (equal f.name mf.name))
        (prog2$ (er hard? 'Smtlink=>merge-a-function "Trying to merge two functions
  with different function names. Check definition for ~p0 and ~p1~%" fn mfn) (make-func)))
        (formals-alist (make-alist-decl-list mf.formals))
       (returns-alist (make-alist-decl-list mf.returns))
       (long-formals
        (with-fast-alist formals-alist
          (merge-decl-list f.formals formals-alist)))
       (short-formals (fast-alist-clean long-formals))
       (long-returns
        (with-fast-alist returns-alist
          (merge-decl-list f.returns returns-alist)))
       (short-returns (fast-alist-clean long-returns)))
    (change-func mfn
                 :formals (strip-cdrs short-formals)
                 :guard (append f.guard mf.guard)
                 :returns (strip-cdrs short-returns)
                 :expansion-depth f.expansion-depth
                 :uninterpreted f.uninterpreted)))

(skip-proofs
(verify-guards merge-a-function
  :hints (("Goal"
           :in-theory (enable decl-alistp))))
)

(define merge-functions ((added-funcs func-listp) (master-funcs func-alistp))
  :returns (merged-functions func-alistp)
  :measure (len added-funcs)
  :hints (("Goal" :in-theory (enable func-alist-fix)))
  :verify-guards nil
  (b* ((added-funcs (func-alist-fix added-funcs))
       (master-funcs (func-alist-fix master-funcs))
       ((unless (consp added-funcs)) master-funcs)
       ((cons first rest) added-funcs)
       ((cons name fn) first)
       (exist? (hons-get name master-funcs))
       ((unless exist?)
        (merge-functions rest (hons-acons name fn master-funcs)))
       (mfn (cdr exist?))
       (merged-fn (merge-a-function fn mfn)))
    (merge-functions rest (hons-acons name merged-fn master-funcs))))

(skip-proofs
(verify-guards merge-functions
  :hints (("Goal"
           :in-theory (enable func-alist-fix func-alistp))))
)

(define merge-hints ((added-hint maybe-smtlink-hint-p) (master-hint smtlink-hint-p))
  :returns (merged-hints smtlink-hint-p)
  :verify-guards nil
  (b* ((added-hint (maybe-smtlink-hint-fix added-hint))
       (master-hint (smtlink-hint-fix master-hint))
       ((if (equal added-hint nil)) master-hint)
       ((smtlink-hint ah) added-hint)
       ((smtlink-hint mh) master-hint)
       (fn-alist (make-alist-fn-lst mh.functions)))
    (change-smtlink-hint mh
                         :functions (with-fast-alist fn-alist
                                      (merge-functions ah.user-functions fn-alist))
                         :user-functions ah.user-functions
                         :hypotheses (append ah.hypotheses mh.hypotheses)
                         :main-hint (append ah.main-hint mh.main-hint)
                         :int-to-rat ah.int-to-rat
                         :smt-fname ah.smt-fname
                         :rm-file ah.rm-file
                         :smt-params ah.smt-params
                         :smt-cnf ah.smt-cnf)))

(skip-proofs
 (verify-guards merge-hints
   :hints (("Goal"
            :in-theory (enable))))
 )

  (define combine-hints ((raw-user-hints smtlink-hint-syntax-p)
                         (hint smtlink-hint-p))
    :returns (combined-hint smtlink-hint-p)
    (b* ((user-hints (smtlink-hint-syntax-fix raw-user-hints))
         (- (cw "Warning (Smtlink=>combine-hints): Smtlink hint syntax
    violated~% ~q0Therefore user provided Smtlink hint ignored.~%" raw-user-hints))
         (hint (smtlink-hint-fix hint))
         (structured-user-hints (save-user-hints user-hints (make-smtlink-hint)))
         (merged-hint (merge-hints structured-user-hints hint)))
      merged-hint))

  (define process-hint ((cl pseudo-term-listp) (user-hint t))
    :returns (subgoal-lst pseudo-term-list-listp)
    :enabled t
    (b* ((cl (pseudo-term-list-fix cl))
         ((unless (smtlink-hint-syntax-p user-hint)) (list cl))
         (- (cw "user-hint: ~q0" user-hint))
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

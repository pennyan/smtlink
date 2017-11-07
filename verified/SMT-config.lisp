;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (August 4th 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software


(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defconsts" :dir :system)
(include-book "std/strings/top" :dir :system)

(defsection SMT-config
  :parents (verified)
  :short "Define default Smtlink config and custom Smtlink config"

  (defprod smtlink-config
    :parents (SMT-config)
    ((interface-dir stringp :default "" "The directory to the customized Python file")
     (smt-module    stringp :default "" "The file/Module name")
     (smt-class     stringp :default "" "The Python class name")
     (smt-cmd       stringp :default "" "The Python command")
     (pythonpath    stringp :default "" "The PYTHONPATH to libraries")))

(local
 (defthm all-boundp-of-initial-glb
   (implies (state-p x)
            (all-boundp acl2::*initial-global-table*
                        (global-table x)))))

(local
 (defthm boundp-of-system-books-dir
   (implies (state-p state)
            (acl2::f-boundp-global 'acl2::system-books-dir state))
   :hints (("Goal"
            :in-theory (disable all-boundp-of-initial-glb)
            :use ((:instance all-boundp-of-initial-glb (x state)))))))

(defconsts *default-smtlink-config*
  (b* ((sys-dir (f-get-global 'acl2::system-books-dir state))
       ((unless (stringp sys-dir))
        (er hard? 'SMT-config=>*default-smtlink-config* "Failed to find ~
where the system books are."))
       (relative-smtlink-dir "smtlink/z3_interface")
       (interface-dir
        (concatenate 'string sys-dir relative-smtlink-dir)))
    (make-smtlink-config :interface-dir interface-dir
                         :smt-module "ACL2_to_Z3"
                         :smt-class "ACL22SMT"
                         :smt-cmd "/usr/local/bin/python"
                         :pythonpath "")))

;; -----------------------------------------------------------------
;; Define custom config using a defstub
(encapsulate
  (((custom-smt-cnf) => *))
  (local (define custom-smt-cnf () (make-smtlink-config)))
  (defthm smtlink-config-p-of-custom-smt-cnf
    (smtlink-config-p (custom-smt-cnf)))
  )

(define default-smtlink-config ()
  (change-smtlink-config *default-smtlink-config*))


(defattach custom-smt-cnf default-smtlink-config)

;; -----------------------------------------------------------------
;; Define baked-in default config

(defalist string-string-alist
  :key-type string
  :val-type string
  :pred string-string-alistp
  :true-listp t)

;; TODO: This check can check a lot of things.
;; Currently only checking if option is one of the valid ones.
(define check-valid-option ((option stringp) (value stringp))
  :returns (valid? booleanp)
  :ignore-ok t
  (b* (((unless (or (equal option "interface-dir")
                    (equal option "smt-module")
                    (equal option "smt-class")
                    (equal option "smt-cmd")
                    (equal option "pythonpath"))) nil))
    t))

(define extract-=-left-and-right ((lines string-listp))
  :returns (config-alist string-string-alistp)
  :measure (len lines)
  :hints (("Goal" :in-theory (enable str::string-list-fix)))
  (b* ((lines (str::string-list-fix lines))
       ((unless (consp lines)) nil)
       ((cons first rest) lines)
       (extracted-line (str::strtok first (list #\Space #\=)))
       ((unless (and (consp extracted-line) (endp (cddr extracted-line))
                     (stringp (car extracted-line))
                     (stringp (cadr extracted-line))))
        (er hard? 'SMT-config=>extract-=-left-and-right "Smtlink-config wrong ~
  format!~%~q0" first))
       ((list option value &) extracted-line)
       ((unless (check-valid-option option value))
        (er hard? 'SMT-config=>extract-=-left-and-right "There's something
  wrong with the configuration setup in smtlink-config.")))
    (cons `(,(car extracted-line) . ,(cadr extracted-line))
          (extract-=-left-and-right rest))))

(define process-config ((config-str stringp))
  :returns (config-alist string-string-alistp)
  (b* ((lines (str::strtok config-str (list #\Newline)))
       (config-alist (extract-=-left-and-right lines)))
    config-alist))

(define change-smt-cnf ((config-alist string-string-alistp) (default-cnf smtlink-config-p))
  :returns (smt-cnf smtlink-config-p)
  :measure (len config-alist)
  :hints (("Goal" :in-theory (enable string-string-alist-fix)))
  (b* ((config-alist (string-string-alist-fix config-alist))
       (default-cnf (smtlink-config-fix default-cnf))
       ((unless (consp config-alist)) default-cnf)
       ((cons first rest) config-alist)
       ((cons option value) first)
       (new-cnf (cond
                 ((equal option "interface-dir")
                  (change-smtlink-config default-cnf :interface-dir value))
                 ((equal option "smt-module")
                  (change-smtlink-config default-cnf :SMT-module value))
                 ((equal option "smt-class")
                  (change-smtlink-config default-cnf :SMT-class value))
                 ((equal option "smt-cmd")
                  (change-smtlink-config default-cnf :SMT-cmd value))
                 (t (change-smtlink-config default-cnf :PYTHONPATH value)))))
    (change-smt-cnf rest new-cnf)))

(defconsts *smt-cnf*
  (b* ((res (read-file-into-string "~/.smtlink-config/smtlink-config"))
       ((unless res) (default-smtlink-config))
       (config-alist (process-config res)))
    (change-smt-cnf config-alist (default-smtlink-config))))


(define default-smt-cnf () *smt-cnf*)
)

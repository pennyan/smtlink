;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (June 26th 2017)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software
;;

(in-package "SMT")
(include-book "doc-tutorial")
(include-book "doc-dev")

;; ------------------------------------------------------- ;;
;;    Documentation

(include-book "xdoc/save" :dir :system)  ;; load xdoc::save

(defxdoc Smtlink
  :parents (ACL2::top)
  :short "Tutorial and documentation for the ACL2 book, Smtlink."
  :long "<h3>Introduction</h3>
         <p>A framework for integrating external SMT solvers into ACL2 based on
         the @(see ACL2::clause-processor) and the @(tsee ACL2::computed-hint)
         mechanism.</p>

         <h4>Overview</h4>
         <p>@('Smtlink') is a framework for representing suitable ACL2 theorems
         as a SMT (Satisfiability Modulo Theories) formula, and calling SMT
         solvers from within ACL2.  Two phases of translation happen in the
         framework.  The first translation is fully verified using several
         verified clause processor interleaved with computed hints, therefore
         is ensured to be sound.  The second phase involves a partial
         transliteration from ACL2's LISP language to the target SMT solver's
         language.  This phase is done through a trusted clause processor and
         thus is not verified in ACL2 to be sound.</p>

         <p>SMT solvers combine domain-specific techniques together into a SAT
         (Satisfiability) Solver and solves domain-specific satisfiability
         problems.  Typical domain specific procedures include procedures in
         integer and real, linear and non-linear arithmetic, array theory,
         and uninterpreted function theory.  Modern SMT solvers benefit from
         the development of both the SAT solvers and the domain-specific
         techniques and have become very fast at solving some relatively large
         problems.  Like the SAT solvers, SMT solvers are also competing each
         other annually at <a
         href='http://smtcomp.sourceforge.net/'>SMT-COMP</a>.</p>

         <p>@('Smtlink') currently only supports <a
         href='https://github.com/Z3Prover/z3/wiki'>Z3</a>. We will be adding
         an interface to include the <a
         href='http://smtlib.cs.uiowa.edu/'>SMT-LIB</a> in near future.</p>

         <h3>Using Smtlink</h3>
         <h4>Requirements</h4>
         <ul>
         <li>Python 2 is properly installed.</li>
         <li>Z3 is properly installed.</li>
         <li>ACL2 and the system books are properly installed.</li>
         <li>@('Smtlink') uses Unix commands.</li>
         </ul>

         <h4>Build Smtlink</h4>
         <ul>
         <li>Use the Makefile</li>
         <p>Makefile requires three parameters @('ACL2'), @('PYTHON') and
         @('SAVE_PY_TO'). @('ACL2') is the directory where @('ACL2') is
         installed. @('PYTHON') tells @('Smtlink') where to find Python and
         @('SAVE_PY_TO') tells @('Smtlink') where to store generated Python
         scripts, if one chooses to keep the scripts.</p> <ul>
         <li>Go to Smtlink directory</li>
         <li>Run @('make JOBS=... ACL2=... PYTHON=... SAVE_PY_TO=...') to
         generate configurations and certify books</li>
         </ul>

         <li>Without using the Makefile</li>
         <ul>
         <li>Run script py_utils/gen_ACL22SMT.py to generate the ACL22SMT.lisp
         file using command:
         @({
          python gen_ACL22SMT.py z3_interface/ACL2_to_Z3.py ./trusted/z3-py/ACL22SMT.lisp
         })
         </li>
         <li>Run script py_utils/gen_config.py to generate the SMT-config.lisp
         file using command:
         @({
          python gen_config.py -i ./verified/SMT-config-template.lisp -o
         ./verified/SMT-config.lisp -p $PYTHON -z $SAVE_PY_TO
         })
         </li>
         <li>Certify Smtlink by @('cert.pl top')</li>
         </ul>
         </ul>

         <h4>Load and Setup Smtlink</h4>
         <p>To use @('Smtlink'), one needs to include book:</p>
         @({
          (include-book \"Smtlink/top\" :dir :system)
         })
         <p>Then one needs to enable @(tsee acl2::tshell) by doing:</p>
         @({
          (value-triple (tshell-ensure))
         })
         <p>@(tsee value-triple) makes sure such term is an event form and
         therefore is certifiable as a book.</p>

         <p>For a detail description of how to setup and get started using
         @('Smtlink'), see @(tsee tutorial).</p>

         <h3>Reference</h3>
         <p>@('Smtlink') has experienced a great interface and infrastructure
         change since its first publication at ACL2 workshop 2015. But you may
         still find below paper useful in understanding basics of
         @('Smtlink'):</p>

         <p>Yan Peng and Mark R. Greenstreet. <a
         href='https://arxiv.org/abs/1509.06082'>Extending ACL2 with SMT
         Solvers</a>In ACL2 Workshop 2015. October 2015. EPTCS 192. Pages 61-77.</p>")

(xdoc::save "./manual" :redef-okp t)  ;; write the manual

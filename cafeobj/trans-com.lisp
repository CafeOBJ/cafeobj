;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
;;;
;;; Copyright (c) 2000-2015, Toshimi Sawada. All rights reserved.
;;;
;;; Redistribution and use in source and binary forms, with or without
;;; modification, are permitted provided that the following conditions
;;; are met:
;;;
;;;   * Redistributions of source code must retain the above copyright
;;;     notice, this list of conditions and the following disclaimer.
;;;
;;;   * Redistributions in binary form must reproduce the above
;;;     copyright notice, this list of conditions and the following
;;;     disclaimer in the documentation and/or other materials
;;;     provided with the distribution.
;;;
;;; THIS SOFTWARE IS PROVIDED BY THE AUTHOR 'AS IS' AND ANY EXPRESSED
;;; OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
;;; WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
;;; ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
;;; DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
;;; DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE
;;; GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
;;; INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
;;; WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
;;; NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
;;; SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
;;;
(in-package :chaos)
#|==============================================================================
                                 System: CHAOS
                                Module: cafeobj
                              File: trans-com.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; == DESCRIPTION =============================================================
;;; Translators from CafeOBJ toplevel command to Chaos script language.
;;; ----------------------------------------------------------------------------

;;; *****************************
;;; REDUCE/EXEC/PARSE/TEST-REDUCE
;;; *****************************
(defun parse-in-context-modexp-with-term (e)
  (let (modexp
        preterm)
    (if (= 4 (length e)) 
        (progn
          (setq modexp (parse-modexp (cadr (cadr e))))
          (setq preterm (nth 2 e)))
        (progn
          (setq modexp nil)
          (setq preterm (nth 1 e))))
    (values modexp preterm)))

;;; "reduce" [ "in" <Modexp> ":" ] <Term> . 
;;;
(defun parse-reduce-command (e &rest ignore)
  (declare (ignore ignore))
  (multiple-value-bind (modexp preterm)
      (parse-in-context-modexp-with-term e)
    (%reduce* preterm modexp ':red)))

;;; "execute" [ "in" <Modexp> ":" ] <Term> .
;;;
(defun parse-exec-command (e &rest ignore)
  (declare (ignore ignore))
  (multiple-value-bind (modexp preterm)
      (parse-in-context-modexp-with-term e)
    (%reduce* preterm modexp ':exec)))

(defun parse-exec+-command (e &rest ignore)
  (declare (ignore ignore))
  (multiple-value-bind (modexp preterm)
      (parse-in-context-modexp-with-term e)
    (%reduce* preterm modexp ':exec+)))

;;; "bred" [ "in" <Modexp> ":" ] <Term> .
;;;
(defun parse-bred-command (e &rest ignore)
  (declare (ignore ignore))
  (multiple-value-bind (modexp preterm)
      (parse-in-context-modexp-with-term e)
    (%reduce* preterm modexp ':bred)))

;;; "parse" [ "in" <Modexp> ":" ] <Term> .
;;;
(defun parse-parse-command (e &rest ignore)
  (declare (ignore ignore))
  (multiple-value-bind (modexp preterm)
      (parse-in-context-modexp-with-term e)
    (%parse* preterm modexp)))

;;; "test {reduce | exec | bred} "
;;;  [ "in" <Modexp> ":" ] <Term> :expect <Term> .
;;;
(defun parse-test-reduction (e &rest ignore)
  (declare (ignore ignore))
  (let ((mode-spec (second e))
        (mode nil))
    (case-equal mode-spec
      (("exec" "execute") (setq mode :exec))
      (("reduce" "red") (setq mode :red))
      (("behavioural-reduce" "bred") (setq mode :bred))
      (t (with-output-chaos-error ('invalid-op)
           (format t "invalid `test' command option ~S" mode))
         ))
    (setq e (cddr e))
    (let ((modexp nil)
          (preterm nil)
          (expect nil))
      (cond ((and (consp (car e)) (equal "in" (caar e)))
             (setf modexp (parse-modexp (second (car e))))
             (setf preterm (second e))
             (setf expect (fourth e)))
            (t (setf modexp nil)
               (setf preterm (first e))
               (setf expect (third e))))
      (%test-reduce* preterm expect modexp mode))))

;;; ****
;;; TRAM
;;; ****
(defun parse-tram-command (inp &rest ignore)
  (declare (ignore ignore))
  (let ((args (cadr inp))
        (command nil))
    (case-equal (car inp)
      (("red" "reduce") (setq command :reduce))
      (("exec" "execute") (setq command :execute))
      (("compile") (setq command :compile))
      (("reset") (setq command :reset))
      (otherwise (with-output-chaos-error ()
                   (format t "unknown tram command ~a" (car inp)))))
    (if (eq command :compile)
        (let ((debug nil))
          (loop
           (case-equal (car args)
             (("-a" "-all" "-e" "-exec")
              (setq command :compile-all)
              (setq args (cdr args)))
             (("-d" "-debug")
              (setq debug t)
              (setq args (cdr args)))
             (t (return nil))))
          (%make-tram :command command :modexp args :debug debug))
        (multiple-value-bind (modexp preterm)
            (parse-in-context-modexp-with-term inp)
          (%make-tram :command command :modexp modexp :term preterm)))))
          
;;; ********
;;; AUTOLOAD
;;; ********
(defun parse-autoload-command (inp &rest ignore)
  (declare (ignore ignore))
  (let ((mod-name (second inp))
        (file (third inp)))
    (%autoload* mod-name file)))

;;;
;;; NO AUTOLOAD
;;;
(defun parse-no-autoload-command (inp &rest ignore)
  (declare (ignore ignore))
  (let ((mod-name (second inp)))
    (%no-autoload* mod-name)))

;;; ******
;;; CBREAD
;;; ******
;;; cbred [in <Modexp> : ] LHS = RHS .
;;;
(defun parse-cbred-command (toks &rest ignore)
  (declare (ignore ignore))
  (multiple-value-bind (modexp preterm)
      (parse-in-context-modexp-with-term toks)
    (let ((lhs nil)
          (rhs nil))
      ;;
      (loop (when (or (null preterm)
                      (member (car preterm)
                              '("=" "=b=" "==") :test #'equal))
              (return))
        (push (car preterm) lhs)
        (setq preterm (cdr preterm)))
      (setq lhs (nreverse lhs))
      (setq rhs (cdr preterm))
      (unless (and lhs rhs)
        (with-output-chaos-error ('invalid-command-form)
          (princ "cbred: syntax error: ")
          (princ toks)))
      (%cbred* modexp lhs rhs))))

;;; *******
;;; LOOK UP
;;; *******
(defun parse-in-context-modexp-with-name (e)
  (let (modexp
        name)
    (setq e (cddr e))
    (if (cdr e)
        (progn
          (setq modexp (parse-modexp (second (first e))))
          (setq name (second e)))
        (progn
          (setq modexp nil)
          (setq name (first e))))
    (values modexp name)))

(defun parse-look-up-command (e &rest ignore)
  (declare (ignore ignore))
  (multiple-value-bind (modexp name)
      (parse-in-context-modexp-with-name e)
    (%look-up* name modexp)))

;;; *****
;;; SCASE
;;; *****
;;; scase (<Term>) in (<Modexp>) as <Name> { ... } : <GoalTerm> .
;;; ("scase" "(" ("1" "==" "2") ")" "in" "(" ("NAT") ")" "as" "NAT-C1" "{" <ModElements> "}" ":" ("1" "==" "2") ".") 
;;;     0    1         2        3    4   5     6     7   8      9      10      11        12  13        14
(defun parse-case-command (expr &rest ignore)
  (declare (ignore ignore))
  (let ((case-term (nth 2 expr))
        (modexpr (parse-modexp (nth 6 expr)))
        (name (nth 9 expr))
        (body (nth 11 expr))
        (goal (nth 14 expr)))
    (when (atom body) 
      (setq body nil)
      (setq goal (nth 13 expr)))
    (%scase* case-term modexpr name body goal)))

;;; *********
;;; LISP/EVAL
;;; *********
(defun parse-eval-lisp (inp)
  (%lisp-eval* (cadr inp)))

;;; ************ 
;;; EVAL (META)
;;; ************
(defun parse-meta-eval (inp)
  (%eval* (cadr inp)))

;;; ************************
;;; INSTANTIATION by `make'
;;; ************************

(defun parse-make-command (inp)
  (let ((name (nth 1 inp))
        (modexp (nth 3 inp)))
    (%module-decl* name
                   :module
                   :user
                   (list (%import* :protecting (parse-modexp modexp))))))

;;; *****
;;; INPUT
;;; *****
(defun parse-input-command (inp)
  (cadr inp))

;;; ****
;;; SAVE
;;; ****
(defparameter _save-pat (%save* 'file))

(defun parse-save-command (inp)
  (setf (%save-file _save-pat) (cadr inp))
  _save-pat)

;;; *******
;;; RESTORE
;;; *******
;;; restore definitions of module from file (saved by `save' command).
(defvar _restore-pat (%restore* 'file))

(defun parse-restore-command (inp)
  (setf (%restore-file _restore-pat) (cadr inp))
  _restore-pat)

;;; *****
;;; RESET
;;; *****
;;; recover definitions of modules in prelude.
(defvar _reset-pat (%reset*))

(defun parse-reset-command (&rest inp)
  (declare (ignore inp))
  _reset-pat)

;;; **********
;;; FULL-RESET
;;; **********
(defvar _full-reset-pat (%full-reset*))

(defun parse-full-reset-command (&rest inp)
  (declare (ignore inp))
  _full-reset-pat)

(defun parse-prelude-command (inp)
  (%load-prelude* (cadr inp) 'parse-cafeobj-input))

;;; ********
;;; COMMENTS
;;; ********
(defun parse-comment-command (inp)
  (%dyna-comment* (cons (car inp) (cdr inp))))

;;; ****
;;; OPEN
;;; ****
(defvar _open-pat (%open-module* 'modexp))

(defun parse-open-command (inp)
  (let ((modexp (second inp)))
    (if modexp
        (setf (%open-module-modexp _open-pat) (parse-modexp modexp))
      (setf (%open-module-modexp _open-pat) nil))
    _open-pat))

;;; *****
;;; CLOSE
;;; *****
(defvar _close-pat (%close-module*))

(defun parse-close-command (&rest ignore)
  (declare (ignore ignore))
  _close-pat)

;;; *************
;;; INSPECT-TERM
;;; *************

(defun parse-inspect-term-command (inp)
  (declare (ignore inp))
  (%inspect-term*))

;;; ***
;;; PWD
;;; ***
(defvar _pwd-pat (%pwd*))

(defun parse-pwd-command (inp)
  (declare (ignore inp))
  _pwd-pat)

;;; **
;;; LS
;;; **
(defvar _ls-pat (%ls* 'dir))

(defun parse-ls-command (inp)
  (setf (%ls-dir _ls-pat) (cadr inp))
  _ls-pat)

;;; **************
;;; ! SHELL ESCAPE
;;; **************
(defvar _shell-pat (%shell* 'command))

(defun parse-shell-command (inp)
  (let ((command (cadr inp)))
    (setf (%shell-command _shell-pat) command)
    _shell-pat))

;;; **
;;; CD
;;; **
(defvar _cd-pat (%cd* 'directory))

(defun parse-cd-command (inp)
  (setf (%cd-directory _cd-pat) (cadr inp))
  _cd-pat)

;;; *****
;;; PUSHD
;;; *****
(defvar _pushd-pat (%pushd* 'directory))

(defun parse-pushd-command (inp)
  (when (>= (length inp) 3)
    (with-output-chaos-error ('invalid-arg)
      (format t "too many args ~s" (cdr inp))))
  (setf (%pushd-directory _pushd-pat) (cadr inp))
  _pushd-pat)

;;; ****
;;; POPD
;;; ****
(defvar _popd-pat (%popd* nil))
(defun parse-popd-command (inp)
  (when (>= (length inp) 3)
    (with-output-chaos-error ('invalid-arg)
      (format t "too many args ~s" (cdr inp))))
  (let ((num (and (cadr inp) (parse-integer (cadr inp) :junk-allowed t))))
    (if num
        (setf (%popd-num _popd-pat) (cadr inp))
      (setf (%popd-num _popd-pat) nil))
    (eval-ast _popd-pat)
    (setf (%popd-num _popd-pat) nil)
    _popd-pat))

;;; ****
;;; DIRS
;;; ****
(defvar _dirs-pat (%dirs*))
(defun parse-dirs-command (inp)
  (declare (ignore inp))
  _dirs-pat)

;;; *****************
;;; PROTECT/UNPROTECT
;;; *****************

(defvar _protect-pat (%protect* 'module :set))

(defun parse-protect-command (inp)
  (setf (%protect-module _protect-pat) (cadr inp))
  _protect-pat)

(defvar _unprotect-pat (%protect* 'module :unset))

(defun parse-unprotect-command (inp)
  (setf (%protect-module _unprotect-pat) (cadr inp))
  _unprotect-pat)

;;; *****************
;;; SHOW/DESCRIBE/SET
;;; *****************
(defvar _select-pat (%select* 'modexp))
(defvar _show-pat (%show* 'args))
(defvar _desc-pat (%describe* 'args))

(defun parse-show-command (inp)
  (let ((tag (car inp))
        (args (cdr inp)))
    (cond ((equal "select" tag)
           (setf (%select-modexp _select-pat) args)
           _select-pat)
          ((member tag '("show" "sh") :test #'equal)
           (setf (%show-args _show-pat) args)
           _show-pat)
          ((member tag '("describe" "desc") :test #'equal)
           (setf (%describe-args _desc-pat) args)
           _desc-pat)
          (t :help))))

;;; ***
;;; SET
;;; ***
(defvar _set-pat (%set* 'switch 'value))

(defun parse-set-command (inp)
  (let ((dat (cadr inp)))
    (let ((which (car dat))
          (value (cdr dat)))
      (setf (%set-switch _set-pat) which)
      (setf (%set-value _set-pat) value)
      _set-pat)))

;;; *******
;;; PROVIDE
;;; *******
(defvar _provide-pat (%provide* 'feature))

(defun parse-provide-command (inp)
  (setf (%provide-feature _provide-pat) (cadr inp))
  _provide-pat)

;;; *******
;;; REQUIRE
;;; *******
(defvar _require-pat (%require* 'feature 'cafeobj-input 'file))

(defun parse-require-command (inp)
  (setf (%require-feature _require-pat) (caadr inp))
  (setf (%require-file _require-pat) (cadadr inp))
  _require-pat)

;;; **********
;;; REGULARIZE
;;; **********
(defparameter _regularize-pat (%regularize* 'modexp))

(defun parse-regularize-command (inp)
  (setf (%regularize-modexp _regularize-pat) (cadr inp))
  _regularize-pat)

;;; **************
;;; CHECK <Things>
;;; **************

;; (%check* 'what 'args))
(defun parse-check-command (inp)
  (let ((dat (cadr inp)))
    (let ((it (car dat)))
      (case-equal it
                  (("reg" "regular" "regularity")
                   (%check* :regularity (cdr dat)))
                  (("lazy" "laziness" "strict" "strictness")
                   (%check* :strictness (cdr dat)))
                  (("compat" "compatibility")
                   (%check* :compatibility (cdr dat)))
                  (("coherency" "coherent" "coh" "coherence")
                   (%check* :coherency (cdr dat)))
                  (("sensible" "sensibleness")
                   (%check* :sensible (cdr dat)))
                  (("rewriting" "rew")
                   (%check* :rew-coherence (cdr dat)))
                  (("invariance" "inv")
                   (%check* :invariance (cdr dat)))
                  (("safety")
                   (%check* :safety (cdr dat)))
                  (("refinement" "refine")
                   (%check* :refinement (cdr dat)))
                  (("?" "help" ":?" ":help")
                   (cafeobj-check-help)
                   (return-from parse-check-command t))))))

;;; 
;;; CHECK HELP
;;; 

(defun cafeobj-check-help (&rest ignore)
  (declare (ignore ignore))
  (format t "~%  check {reg | regularity} [<Modexp>]")
  (format t "~&~8Tcheck <Modexp> (or current module's) signagture is regular or not.")
  (format t "~&  check {compat | compatibility} [<Modexp>]")
  (format t "~&~8Tcheck <Modexp> (or current module) is compatible or not.")
  (format t "~&  check {lazy | laziness} [<Operator>]")
  (format t "~&~8Tcheck strictness of <Operator>")
  (format t "~& check {coh | coherency | coherence} <Operator>")
  (format t "~&~8Tcheck if operator is behaviouraly coherent")
  (format t "~& check {sensible | sensibleness} [<Modexp>]")
  (format t "~&~8Tcheck if the signature of the module is sensible or not.")
  (format t "~& check {rewriting | rew} {coh | coherency} [<Modexp>]")
  (format t "~&~8Tcheck if trans axioms and equations are coherent of not.")
  )

;;; *******
;;; DRIBBLE
;;; *******

(defun parse-dribble-command (inp)
  (let ((file (cadr inp)))
    (if (equal file ".")
        (%dribble* nil)
      (%dribble* file))))

;;; *********
;;; CONTINUIE
;;; *********

(defun parse-continue-command (args)
  (when (cddr args)
    (with-output-chaos-error ('invalid-arg)
      (format t "invalid args ~a" args)))
  (let ((num-tok (cadr args))
        (num 1))
    (when num-tok
      (setq num (read-from-string num-tok)))
    (unless (and (integerp num)
                 (> num 0))
      (with-output-chaos-error ('invalid-arg)
        (format t "continue count must be positive integer, but ~a is given."
                num-tok)))
    (%continue* num)))

;;; ****
;;; NAME
;;; ****
(defun parse-name-command (inp)
  (let ((modexp (second inp))
        (ast (%inspect* nil)))
    (when modexp
      (setf (%inspect-modexp ast) (parse-modexp modexp)))
    ast))

;;; *******
;;; VERSION
;;; *******
(defun parse-version-command (&rest ignore)
  (declare (ignore ignore))
  cafeobj-version)

;;; ******************
;;; MODULE Constructs.
;;; ******************

;;; it is an error unless a module is open.
(defun cafeobj-eval-module-element-proc (inp)
  (let ((last-result nil))
    (if *open-module*
        (with-in-module ((get-context-module))
          (multiple-value-bind (type ast)
              (parse-module-element inp)
            (declare (ignore type))
            (dolist (a ast last-result)
              (setq last-result (eval-ast a)))))
      (with-output-chaos-warning ()
        (princ "no module open.")))))

;;; ******
;;; GENDOC
;;; ******
(defparameter _gendoc-pat (%gendoc* 'file))

(defun parse-gendoc-command (inp)
  (setf (%gendoc-file _gendoc-pat) (cadr inp))
  _gendoc-pat)

;;; EOF

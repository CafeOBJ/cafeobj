;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: command-proc.lisp,v 1.11 2010-07-15 04:40:55 sawada Exp $
#|==============================================================================
                             System: CHAOS
                            Module: cafeobj
                         File: command-proc.lisp
==============================================================================|#
(in-package :chaos)
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;;=============================================================================
;;; DESCRIPTION:
;;;          Specific CafeOBJ top level command processors.
;;;
;;;=============================================================================

#|| NOT USED NOW

(declaim (inline make-command-key))
#-gcl
(defun make-command-key (key)
  (if (stringp key)
      (intern key)
    key))
#+gcl
(si::define-inline-function make-command-key (key)
  (if (stringp key)
      (intern key)
    key))

(defun define-cafeobj-command (key-list proc)
  (when (atom key-list) (setq key-list (list key-list)))
  (dolist (key key-list)
    (let ((key-value (make-command-key key)))
      (setf (get key-value ':cafeobj-command) proc))))

(defun get-cafeobj-command-processor (key)
  (get (make-command-key key) ':cafeobj-command))

||#

;;; SPECIFIC COMMAND PROCESSORS ************************************************

(eval-when (eval load compile)
  (defmacro with-no-chaos-counter-parts ((name) &body body)
    ` (block body
        (when (and *dribble-ast* *dribble-stream*)
          (format *dribble-stream* "~&;; ** ~s has no chaos couterparts.~%" ,name))
        (when *eval-ast*
          ,@body))))

;;; *********
;;; CONTROL-D
;;; *********
;;; specialy handled for interacting with CafeOBJ server.

(defun cafeobj-eval-control-d (&rest ignore)
  (declare (ignore ignore))
  (when *eval-ast*
    (princ eof-char)
    (force-output)))

;;; ******
;;; PROMPT
;;; ******
;;; sets interpreter prompt pattern.
;;; prompt {reset | sys | system} -- use system's standard prompt pattern.
;;;   else use specified pattern as prompt.
;;; *NOTE* there's no counterparts in Chaos Language.

(defun cafeobj-eval-prompt (inp)
  (with-no-chaos-counter-parts (inp)
    (let ((prompt (cadr inp)))
      (unless (cdr prompt)
        (setq prompt (car prompt)))
      (if prompt
          (case-equal prompt    
                      (("reset" "sys" "system") (setq *prompt* 'system))
                      (t (setq *prompt* prompt)))
        (setq *prompt* 'none)))))

;;; *********************
;;; START TCL/TK GUI proc .* OBSOLATE *
;;; *********************
;;; now obsolate. 

(defun start-ui-proc (inp)
  (declare (ignore inp))
  (with-output-simple-msg ()
    (princ "sorry, start-ui is now obsolate..."))
  (return-from start-ui-proc nil)
  #||
  (and (fboundp 'start-ui) (start-ui))
  ||#
  )

;;; ******************
;;; MODULE DECLARATION
;;; ******************

(defun cafeobj-eval-module-proc (inp)
  (let ((ast (process-module-declaration-form inp)))
    (eval-ast ast)))

;;; ******************
;;; MODULE Constructs.
;;; ******************

(defun cafeobj-eval-module-element-proc (inp)
  (if *open-module*
      (with-in-module (*last-module*)
        (let ((ast (parse-module-element inp)))
          (dolist (a ast)
            (eval-ast a))))
    (with-output-chaos-warning ()
      (princ "no module open."))))

;;; ****************
;;; VIEW DECLARATION.
;;; ****************

(defun cafeobj-eval-view-proc (inp)
  (let ((ast (process-view-declaration-form inp)))
    (eval-ast ast)))

;;; *********
;;; REDUCTION
;;; *********
;;; rewrite only using equations as rewrite rules.
;;; 

(defun cafeobj-eval-reduce-proc (inp)
  (let ((ast (process-reduce-command inp)))
    (eval-ast ast)))

;;; *********************
;;; BEHAVIOURAL-REDUCTOIN
;;; *********************

(defun cafeobj-eval-bred-proc (inp)
  (let ((ast (process-bred-command inp)))
    (eval-ast ast)))

;;;; ******************************
;;;; CIRCULAR COINDUCTIVE REWRITING
;;;; ******************************

(defun cafeobj-eval-cbred-proc (inp)
  (let ((ast (process-cbred-command inp)))
    (eval-ast ast)))

;;; ***********
;;; REDUCE-LOOP
;;; ***********
;;; not yet properly implemented.

(defun cafeobj-eval-reduce-loop-proc (inp)
  (let ((arg (cadr inp)))
    (red-loop (if (equal "." arg) *last-module* arg))))

;;; **************
;;; TEST REDUCTION
;;; **************

(defun cafeobj-eval-test-reduce-proc (inp)
  (let ((ast (process-test-reduction inp)))
    (eval-ast ast)))

;;; ****
;;; EXEC
;;; ****
;;; rewrite using both equations and rules.

(defun cafeobj-eval-exec-proc (inp)
  (let ((ast (process-exec-command inp)))
    (eval-ast ast)))

;;; EXEC+
(defun cafeobj-eval-exec+-proc (inp)
  (let ((ast (process-exec+-command inp)))
    (eval-ast ast)))

;;; ********
;;; LANGUAGE *NOT YET*
;;; ********
(defun cafeobj-eval-lang-proc (inp)
  (let ((arg (cadr inp)))
    (red-loop (if (equal "." arg) *last-module* arg) t)))

;;; **********
;;; PARSE TERM
;;; **********

(defun cafeobj-eval-parse-proc (inp)
  (let ((ast (process-parse-command inp)))
    (eval-ast ast)))

;;; ***********
;;; LISP Escape
;;; ***********

(defun cafeobj-eval-lisp-proc (inp)
  (let* ((ast (%lisp-eval* (cadr inp)))
         (res (eval-ast ast)))
    (setq $ res)
    (unless *cafeobj-input-quiet*
      (let ((*print-case* :upcase))
        (format t "~&~s -> ~s" (cadr inp) res)))))

(defun cafeobj-eval-lisp-q-proc (inp)
  (let ((*cafeobj-input-quiet* t))
    (cafeobj-eval-lisp-proc inp)))

;;; ************ 
;;; EVAL (META)
;;; ************
(defun cafeobj-meta-eval-proc (inp)
  (let ((ast (%eval* (cadr inp))))
    (eval-ast ast)))

;;; ************************
;;; INSTANTIATION by `make'
;;; ************************

(defun cafeobj-eval-make-proc (inp)
  (let ((name (nth 1 inp))
        (modexp (nth 3 inp)))
    (eval-ast
     (%module-decl* name
                    :module
                    :user
                    (list (%import* :protecting (parse-modexp modexp)))))))

;;; *****
;;; INPUT
;;; *****
;;; reading in file.

(defvar .in-in. nil)
(declaim (special .in-in.))

(defun cafeobj-eval-input-proc (inp)
  (let ((file (cadr inp)))
    (!input-file file)))

(defun !input-file (file)
  (when *eval-ast*
    (unless (or (at-top-level) *cafeobj-input-quiet*)
      (format t "~&-- reading in file  : ~a~%" (namestring file))))
  (setq .in-in. t)
  (with-chaos-top-error ()
    (with-chaos-error ()
      (eval-ast
       (%input* file *chaos-libpath*
                'process-cafeobj-input '(".bin" ".cafe" ".mod") nil))
      ))
  ;; (cafeobj-input file)
  (when *eval-ast*
    (unless (or (at-top-level) *cafeobj-input-quiet*)
      (format t "~&-- done reading in file: ~a~%" (namestring file)))))

;;; ****
;;; SAVE
;;; ****
(defvar _save-pat (%save* 'file))

(defun cafeobj-eval-save-proc (inp)
  (setf (%save-file _save-pat) (cadr inp))
  (eval-ast _save-pat))

;;; *******
;;; RESTORE
;;; *******
;;; restore definitions of module from file (saved by `save' command).
(defvar _restore-pat (%restore* 'file))

(defun cafeobj-eval-restore-proc (inp)
  (setf (%restore-file _restore-pat) (cadr inp))
  (eval-ast _restore-pat))

;;; *****
;;; RESET
;;; *****
;;; recover definitions of modules in prelude.
(defvar _reset-pat (%reset*))

(defun cafeobj-eval-reset-proc (&rest inp)
  (declare (ignore inp))
  (eval-ast _reset-pat))

;;; **********
;;; FULL-RESET
;;; **********
(defvar _full-reset-pat (%full-reset*))

(defun cafeobj-eval-full-reset-proc (&rest inp)
  (declare (ignore inp))
  (eval-ast _full-reset-pat))

;;; ***********
;;; SAVE-SYSTEM
;;; ***********
;;; save current status CafeOBJ interpreter as a executable file.

(defun save-cafeobj (&optional (file "./xbin/cafeobj.exe"))
  (setq -cafeobj-load-time- (get-time-string))
  (set-cafeobj-standard-library-path)
  (eval-ast (%save-chaos* 'cafeobj-top-level file)))

(defun save-cafeobj-no-top (&optional (file "./xbin/cafeobj.exe"))
  (setq -cafeobj-load-time- (get-time-string))
  (set-cafeobj-standard-library-path)
  (eval-ast (%save-chaos* nil file)))

(defun cafeobj-eval-save-system (inp)
  (let ((file (cadr inp)))
    (if (equal file ".")
        (save-cafeobj-no-top)
      (save-cafeobj-no-top file))))

;;; **********
;;; CLEAR-MEMO
;;; **********
(defun cafeobj-eval-clear-memo-proc (&rest ignore)
  (declare (ignore ignore))
  (clear-term-memo-table *term-memo-table*))

;;; *******
;;; PRELUDE
;;; *******
;;; reading in prelude file

;;; defined in cafeobjvar.lisp
;;; (defvar *cafeobj-standard-prelude-path* nil)

(defun cafeobj-eval-prelude-proc (inp)
  (setq *cafeobj-standard-prelude-path*
    (with-chaos-error ()
      (eval-ast (%load-prelude* (cadr inp) 'process-cafeobj-input)))))

(defun cafeobj-eval-prelude-proc+ (inp)
  (let ((f (cafeobj-probe-file (cadr inp))))
    (unless f
      (with-output-chaos-error ()
        (format t "no such file ~a" (cadr inp))))
    ;;
    (setq *cafeobj-standard-prelude-path* f)
    ;; now not uses AST
    ;; (eval-ast (%load-prelude* f 'process-cafeobj-input))
    (load-prelude+ f 'process-cafeobj-input)))

;;; *********
;;; CALL-THAT
;;; *********
;;; not yet implemented.

(defun cafeobj-eval-call-that-proc (inp)
  (declare (ignore inp))
  (format t "~%Sorry, but `call-that' is not implemented yet.")
  t)

;;; **************************
;;; LET appearing at top level.
;;; **************************

(defun cafeobj-eval-let-proc (inp)
  (eval-ast (process-let-declaration-form inp)))

;;; ********
;;; Comments
;;; ********

(defun cafeobj-eval-comment-proc (inp)
  (declare (ignore inp))
  nil)

(defun cafeobj-eval-dyna-comment-proc (inp)
  (eval-ast (%dyna-comment* (cons (car inp) (cdr inp)))))

;;; ****
;;; OPEN
;;; ****
(defvar _open-pat (%open-module* 'modexp))

(defun cafeobj-eval-open-proc (inp)
  (let ((modexp (second inp)))
    (if modexp
        (setf (%open-module-modexp _open-pat) (parse-modexp modexp))
      (setf (%open-module-modexp _open-pat) nil))
    (eval-ast _open-pat)))

;;; *****
;;; CLOSE
;;; *****
(defvar _close-pat (%close-module*))

(defun cafeobj-eval-close-proc (&rest ignore)
  (declare (ignore ignore))
  (eval-ast _close-pat))

;;; *****
;;; START
;;; *****

(defun cafeobj-eval-start-proc (inp)
  (eval-ast (parse-start-command inp)))

;;; *****
;;; APPLY
;;; *****

(defun cafeobj-eval-apply-proc (inp)
  (eval-ast (parse-apply-command inp)))

;;; ******
;;; CHOOSE
;;; ******

(defun cafeobj-eval-choose-proc (inp)
  (eval-ast (parse-choose-command inp)))

;;; *****
;;; MATCH
;;; *****

(defun cafeobj-eval-match-proc (inp)
  (eval-ast (parse-match-command inp)))

;;; ****
;;; FIND
;;; ****

(defun cafeobj-eval-find-proc (inp)
  (eval-ast (parse-find-command inp)))

;;; ****
;;; HELP
;;; ****

(defun cafeobj-eval-help-proc (inp)
  (cafeobj-top-level-help inp))

(defun cafeobj-eval-what-proc (inp)
  (cafeobj-what-is inp))

;;; ***
;;; PWD
;;; ***
(defvar _pwd-pat (%pwd*))

(defun cafeobj-eval-pwd-proc (inp)
  (declare (ignore inp))
  (eval-ast _pwd-pat))

;;; **
;;; LS
;;; **
(defvar _ls-pat (%ls* 'dir))

(defun cafeobj-eval-ls-proc (inp)
  (setf (%ls-dir _ls-pat) (cadr inp))
  (eval-ast _ls-pat))

;;; ************
;;; SHELL ESCAPE
;;; ************
(defvar _shell-pat (%shell* 'command))

(defun cafeobj-eval-shell-proc (inp)
  (let ((command (cadr inp)))
    (setf (%shell-command _shell-pat) command)
    (eval-ast _shell-pat)))

;;; **
;;; CD
;;; **
(defvar _cd-pat (%cd* 'directory))

(defun cafeobj-eval-cd-proc (inp)
  (setf (%cd-directory _cd-pat) (cadr inp))
  (eval-ast _cd-pat))

;;; *****
;;; PUSHD
;;; *****
(defvar _pushd-pat (%pushd* 'directory))
(defun cafeobj-eval-pushd-proc (inp)
  (when (>= (length inp) 3)
    (with-output-chaos-error ('invalid-arg)
      (format t "too many args ~s" (cdr inp))))
  (setf (%pushd-directory _pushd-pat) (cadr inp))
  (eval-ast _pushd-pat))

;;; ****
;;; POPD
;;; ****
(defvar _popd-pat (%popd* nil))
(defun cafeobj-eval-popd-proc (inp)
  (when (>= (length inp) 3)
    (with-output-chaos-error ('invalid-arg)
      (format t "too many args ~s" (cdr inp))))
  (setf (%popd-num _popd-pat) (cadr inp))
  (eval-ast _popd-pat)
  (setf (%popd-num _popd-pat) nil))

;;; ****
;;; DIRS
;;; ****
(defvar _dirs-pat (%dirs*))
(defun cafeobj-eval-dirs-proc (inp)
  (declare (ignore inp))
  (eval-ast _dirs-pat))

;;; *****************
;;; PROTECT/UNPROTECT
;;; *****************

(defvar _protect-pat (%protect* 'module :set))

(defun cafeobj-eval-protect-proc (inp)
  (setf (%protect-module _protect-pat) (cadr inp))
  (eval-ast _protect-pat))

(defvar _unprotect-pat (%protect* 'module :unset))

(defun cafeobj-eval-unprotect-proc (inp)
  (setf (%protect-module _unprotect-pat) (cadr inp))
  (eval-ast _unprotect-pat))

;;;*****************************************************************************
;;; "show" "sh" "mod" "set" "do" 
;;;_____________________________________________________________________________

(defun cafeobj-eval-show-proc (inp)
  (cafeobj-process-show-commands inp))

(defun cafeobj-eval-set-proc (inp)
  (cafeobj-process-set-commands inp))

(defun cafeobj-eval-do-proc (inp)
  (with-no-chaos-counter-parts (inp)
    (format t "~&`do' is not implemented yet.")))

;;; *****************
;;; SHOW/DESCRIBE/SET
;;; *****************
(defvar _select-pat (%select* 'modexp))
(defvar _show-pat (%show* 'args))
(defvar _desc-pat (%describe* 'args))

(defun cafeobj-process-show-commands (inp)
  (let ((tag (car inp))
        ;; (dat (cadr inp))
        (args (cdr inp)))
    (cond ((equal "select" tag)
           (setf (%select-modexp _select-pat) args)
           (eval-ast _select-pat))
          ((member tag '("show" "sh") :test #'equal)
           (setf (%show-args _show-pat) args)
           (eval-ast _show-pat))
          ((member tag '("describe" "desc") :test #'equal)
           (setf (%describe-args _desc-pat) args)
           (eval-ast _desc-pat))
          (t (error "Internal error, invalid command ~s" inp)))))

;;; ***
;;; SET
;;; ***
(defvar _set-pat (%set* 'switch 'value))

#||
(defun cafeobj-process-set-commands (inp)
  (let ((dat (cadr inp)))
    (let* ((parity (car (last dat)))
           (which (if (member parity '("on" "off" "yes" "no") :test #'equal)
                      (butlast dat)
                    dat)))
      (setf (%set-switch _set-pat) which)
      (setf (%set-value _set-pat) parity)
      (eval-ast _set-pat))))
||#

(defun cafeobj-process-set-commands (inp)
  (let ((dat (cadr inp)))
    (let ((which (car dat))
          (value (cdr dat)))
      (setf (%set-switch _set-pat) which)
      (setf (%set-value _set-pat) value)
      (eval-ast _set-pat))))

;;; OBSOLATE
#||
(defun process-do-command (inp)
  (let ((tag (car inp))
        (dat (cadr inp)))
    (cond ((equal '("gc") dat)
           #+KCL (gbc t)
           #+(or LUCID CMU) (ext:gc)
           )
          ;;
          ((equal '("clear" "memo") dat) (memo-clean))
          ((equal "save" (car dat)) (cafeobj-save-status (cdr dat)))
          ((equal "restore" (car dat)) (cafeobj-restore-status (cdr dat)))
          ((equal '("?") dat)
           (princ "  ") (princ tag) (princ " [gc|clear memo] .") (terpri)
           (princ "  ") (princ tag) (princ " [save|restore] <Name> .") (terpri)
           )
          (t (with-output-chaos-warning ()
               (princ "`do' option ")
               (princ dat)
               (princ " not recognized") (terpri)))
          )))

||#

;;; *******
;;; PROVIDE
;;; *******
(defvar _provide-pat (%provide* 'feature))

(defun cafeobj-provide-proc (inp)
  (setf (%provide-feature _provide-pat) (cadr inp))
  (eval-ast _provide-pat))

;;; *******
;;; REQUIRE
;;; *******
(defvar _require-pat (%require* 'feature 'cafeobj-input 'file))

(defun cafeobj-require-proc (inp)
  (setf (%require-feature _require-pat) (caadr inp))
  (setf (%require-file _require-pat) (cadadr inp))
  (eval-ast _require-pat))

;;;*****************************************************************************
;;; LITTLE SEMANTIC TOOLS
;;;=============================================================================

;;; ********************
;;; REGULARIZE SIGNATURE
;;; ********************
(defvar _regularize-pat (%regularize* 'modexp))

(defun cafeobj-eval-regularize-proc (inp)
  (setf (%regularize-modexp _regularize-pat) (cadr inp))
  (eval-ast _regularize-pat))

;;; **************
;;; CHECK <Things>
;;; **************

;; (defvar _check-pat (%check* 'what 'args))

(defun cafeobj-eval-check-proc (inp)
  (let ((dat (cadr inp)))
    (let ((it (car dat)))
      (eval-ast
       (case-equal it
                   (("reg" "regular" "regularity")
                    (%check* :regularity (cdr dat)))
                   (("lazy" "laziness" "strict" "strictness")
                    (%check* :strinctness (cdr dat)))
                   (("compat" "compatibility")
                    (%check* :compatibility (cdr dat)))
                   (("coherency" "coherent" "coh" "coherence")
                    (%check* :coherency (cdr dat)))
		   (("sensible" "sensibleness")
		    (%check* :sensible (cdr dat)))
		   (("rewriting" "rew")
		    (%check* :rew-coherence (cdr dat)))
                   #+:BigPink
                   (("invariance" "inv")
                    (%check* :invariance (cdr dat)))
                   #+:BigPink
                   (("safety")
                    (%check* :safety (cdr dat)))
                   #+:BigPink
                   (("refinement" "refine")
                    (%check* :refinement (cdr dat)))
                   (("?" "help" ":?" ":help")
                    (cafeobj-check-help)
                    (return-from cafeobj-eval-check-proc t))
                   (t
                    (with-output-chaos-warning ()
                      (format t "Unknown options to \"check\" command: ~a" it)
                      (chaos-to-top))))))))

;;; **********
;;; CHECK HELP
;;; **********

(defun cafeobj-check-help (&rest ignore)
  (declare (ignore ignore))
  (format t "~&  check {reg | regularity} [<Modexp>]")
  (format t "~&~8Tcheck <Modexp> (or current module's) signagture is regular or not.")
  (format t "~&  check {compat | compatibility} [<Modexp>]")
  (format t "~&~8Tcheck <Modexp> (or current module) is compatible or not.")
  (format t "~&  check {lazy | laziness} [<Operator>]")
  (format t "~&~8Tcheck strictness of <Operator>")
  (format t "~& check {coh | coherency | coherence} <Operator>")
  (format t "~&~8Tcheck if operator is behaviouraly coherent")
  (format t "!& check {sensible | sensibleness} [<Modexp>]")
  (format t "~&~8Tcheck if the signature of the module is sensible or not.")
  (format t "~& check {rewriting | rew} coherence [<Modexp>]")
  (format t "~&~8Tcheck if trans axioms and equations are coherent of not.")
  )

;;; *******
;;; DRIBBLE
;;; *******

(defun cafeobj-eval-dribble-proc (inp)
  (let ((file (cadr inp)))
    (if (equal file ".")
        (eval-ast (%dribble* nil))
      (eval-ast (%dribble* file)))))

;;; ***********************
;;; TRAM COMPILER INTERFACE
;;; ***********************

(defun cafeobj-eval-tram-proc (inp)
  (let ((ast (process-tram-command (cdr inp))))
    (eval-ast ast)))

;;; ********
;;; AUTOLOAD
;;; ********
(defun cafeobj-eval-autoload-proc (inp)
  (let ((ast (process-autoload-command (cdr inp))))
    (eval-ast ast)))

;;; DELIMITER
(defun eval-delimiter-proc (pre-args)
  (declare (type list pre-args)
	   (values t))
  (let ((args nil)
	(op nil)
	(ast nil))
    (case-equal (the simple-string (second pre-args))
		("=" (setq op :set))
		("+" (setq op :add))
		("-" (setq op :delete))
		(t (with-output-chaos-error ('internal)
		     (format t "delimiter op given ivalid op ~a" (second pre-args)))))
    (setq pre-args (fourth pre-args))
    (dolist (a pre-args)
      (push a args))
    (setq ast (%delimiter* op (nreverse args)))
    (eval-ast ast)))

(defun eval-show-delimiter (&rest ignore)
  (declare (ignore ignore))
  (lex-show-delimiters *standard-output*))

#|| moved to 
;;; **************************
;;; PigNose Top Level Commands
;;; **************************

(defun cafeobj-eval-sos-proc (inp)
  (let ((ast (process-sos-command (cdr inp))))
    (eval-ast ast)))

(defun cafeobj-eval-db-proc (inp)
  (let ((ast (process-db-command (cdr inp))))
    (eval-ast ast)))

(defun cafeobj-eval-clause-proc (inp)
  (let ((ast (process-clause-command (cdr inp))))
    (eval-ast ast)))

(defun cafeobj-eval-list-proc (inp)
  (let ((ast (process-list-command (cdr inp))))
    (eval-ast ast)))

(defun cafeobj-eval-resolve-proc (inp)
  (let ((ast (process-resolve-command (cdr inp))))
    (eval-ast ast)))
||#

(defun cafeobj-eval-version-proc (&rest ignore)
  (declare (ignore ignore))
  (with-output-simple-msg ()
    (princ cafeobj-version)))

;;; ***************
;;; CHAOS TOP LEVEL
;;; ***************
(defun cafeobj-eval-chaos-proc (args)
  (eval-ast (%chaos* args)))

;;; 
;;; continuie
;;;
(defun cafeobj-eval-continue (args)
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
    (eval-ast (%continue* num))))

;;;
;;; cafeobj-eval-look-up
;;;
(defun cafeobj-eval-look-up (inp)
  (let ((ast (process-look-up-command inp)))
    (eval-ast ast)))

;;;
;;; cafeobj-eval-inspect
;;;
(defun cafeobj-eval-inspect (inp)
  (let ((modexp (second inp))
	(ast (%inspect* nil)))
    (when modexp
      (setf (%inspect-modexp ast) (parse-modexp modexp)))
    (eval-ast ast)))

;;; EOF

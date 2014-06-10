;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: command-top.lisp,v 1.15 2010-06-21 07:23:00 sawada Exp $
#|==============================================================================
                            System: CHAOS
                           Module: cafeobj
                         File: command-top.lisp
==============================================================================|#
(in-package :chaos)
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;;=============================================================================
;;; Declarations/Commands handlers
;;;-----------------------------------------------------------------------------

;;;*****************************************************************************
;;; Top-level utility functions
;;;*****************************************************************************

;;; SCAN ARGUMENTS
;;;_____________________________________________________________________________

;;; CAFEOBJ-PROCESS-ARGS
;;; ** NOTE ** : only supported for GCL based CafeOBJ.
;;;
#+GCL
(defun get-arg-string ()
  (let ((res nil)
        (argc (si::argc)))
    (if (< 1 argc)
        (let ((i 1))
          (while (> argc i)
            (push (si::argv i) res)
            (incf i))))
    (nreverse res)))

#+CMU
(defun get-arg-string ()
  (cdr ext::*command-line-strings*))

#+EXCL
(defun get-arg-string ()
  (cdr (system:command-line-arguments)))

#+sbcl
(defun get-arg-string ()
  (cdr sb-ext:*posix-argv*))

#-(or GCL CMU EXCL sbcl)
(defun get-arg-string ()
  nil)

;;;
(defun cafeobj-process-args (&rest ignore)
  (declare (ignore ignore))
  (catch *top-level-tag*
    (with-chaos-top-error ()
      (with-chaos-error ()
        (setq *cafeobj-load-init-file* t)
        (setq *cafeobj-initial-load-files* nil)
        (setq *cafeobj-initial-prelude-file* nil)
        (let* ((args (get-arg-string))
               (argc (length args)))
	  (declare (type list args))
          (when (< 0 argc)
            (let ((i 0))
              (while (> argc i)
                (case-equal (nth i args)
                            #+CMU
                            (("-core")
                             (incf i 2)) ; ignore this
                            (("-debug")
                             (on-debug)
                             (incf i))
                            (("-parse-debug")
                             (setq *on-parse-debug* t)
                             (incf i))
                            (("-modexp-debug")
                             (setq *on-modexp-debug* t)
                             (incf i))
                            (("-import-debug")
                             (setq *on-import-debug* t))
                            (("-match-debug")
                             (setq *match-debug* t))
                            (("-view-debug")
                             (setq *on-view-debug* t))
                            (("-h" "-help")
                             (cafeobj-interpreter-help)
                             (bye-bye-bye))
                            (("-q")
                             (setq *cafeobj-load-init-file* nil)
                             (incf i))
                            (("-batch")
                             (setq *cafeobj-batch* t)
                             (incf i))
                            (("-no-banner")
                             (setq *cafeobj-no-banner* t)
                             (incf i))
                            (("-prefix")
                             (progn (setq *cafeobj-install-dir*
                                      (nth (incf i) args))
                                    (incf i)
                                    (set-cafeobj-standard-library-path *cafeobj-install-dir*)))
                            (("-p" "-prelude")
                             (if *cafeobj-initial-prelude-file*
                                 (with-output-chaos-warning ()
                                   (format t "more than one prelude files are specified.")
                                   (print-next)
                                   (format t "file ~a is ignored." (nth (incf i) args))
                                   (incf i))
                               (progn (setq *cafeobj-initial-prelude-file*
                                        (nth (incf i) args))
                                      (incf i))))
                            (("+p" "+prelude")
                             (if *cafeobj-secondary-prelude-file*
                                 (with-output-chaos-warning ()
                                   (format t "more than one secondary prelude files are specified:")
                                   (print-next)
                                   (format t "file ~a is ignored." (nth (incf i) args))
                                   (incf i))
                               (progn (setq *cafeobj-secondary-prelude-file*
                                        (nth (incf i) args))
                                      (incf i))))
                            (("-lib" "-l")
                             (let ((lpaths nil))
                               (dolist (x (parse-with-delimiter (nth (incf i) args)
                                                                #\:))
                                 #||
                                 (when (probe-file x)
                                   (push x lpaths))
                                 ||#
                                 (push x lpaths)
                                 )
                               (incf i)
                               (setq *chaos-libpath* (nreverse lpaths))))
                            (("+lib" "+l")
                             (let ((lpaths nil))
                               (dolist (x (parse-with-delimiter (nth (incf i) args)
                                                                #\:))
                                 #||
                                 (when (probe-file x)
                                   (push x lpaths))
                                 ||#
                                 (push x lpaths)
                                 )
                               (incf i)
                               (setq *chaos-libpath*
                                 (append (nreverse lpaths) *chaos-libpath*))))
                            #+ALLEGRO
                            (("-e")
                             (let ((form (nth (incf i) args)))
                               (handler-case
                                   (handler-case
                                       (eval (with-standard-io-syntax
                                               (read-from-string form)))
                                     (error (c)
                                       (warn "~
An error occurred (~a) during the reading or evaluation of -e ~s" c form))))))
                            (t (push (nth i args) *cafeobj-initial-load-files*)
                               (incf i)))))))
        ;; load prelude if need
        (let ((*chaos-quiet* t))
          (when (and *cafeobj-batch* (null *cafeobj-initial-load-files*))
            ;; we don't need loading prelude.
            (return-from cafeobj-process-args nil))
          (if *cafeobj-initial-prelude-file*
              ;; load specified prelude files
              (progn
                (format t "~&-- loading prelude")
                ;;(format t "~&-- do `save-system' for creating system prelude pre-loaded.")
                (setq *cafeobj-standard-prelude-path*
                  (load-prelude *cafeobj-initial-prelude-file* 'process-cafeobj-input)))
            (unless *cafeobj-standard-prelude-path*
              (format t "~&-- loading standard prelude")
              ;;(format t "~&-- do `save-system' for creating system prelude pre-loaded.")
              (setq *cafeobj-standard-prelude-path*
                (load-prelude "std" 'process-cafeobj-input))))
          (when *cafeobj-secondary-prelude-file*
            (format t "~&-- appending prelude")
            (setq *cafeobj-secondary-prelude-path*
              (load-prelude+ *cafeobj-secondary-prelude-file* 'process-cafeobj-input)))
          ;; load site init
          (load-prelude "site-init" 'process-cafeobj-input t)
          )
        ))))

;;; TOP LEVEL HELP
;;;_____________________________________________________________________________

;;; CafeOBJ INTERPRETER OPTIONS
;;;
(defun cafeobj-interpreter-help ()
  (format t "~%Usage: cafeobj [options] files ...")
  (format t "~&Options: [defaults in brackets after descriptions]")
  (format t "~& -help~16Tprint this help message.")
  (format t "~& -q~16Tdo not load user's initialization file.")
  (format t "~& -batch~16Truns in batch mode.")
  (format t "~& -p PATH~16Tstandard prelude file defining modules.")
  (format t "~& +p PATH~16Tadditional prelude file.")
  (format t "~& -l DIR-LIST~16Tset list of pathnames as module search paths. ")
  (format t "~&~16T[ /usr/local/cafeobj/lib:/usr/local/cafeobj/exs ]")
  (format t "~& +l DIR-LIST~16Tadds list of pathnames as mdoule search paths.")
  (format t "~&Files:")
  (format t "~& files are loaded at start up time in order.~%")
  (force-output))

;;; CafeOBJ INTERPRETER TOPLEVEL HELP
;;;
(defun cafeobj-top-level-help (&optional com)
  (cond ((null (cdr com))
         (format t "~&-- CafeOBJ top level commands :")
         (format t "~&-- Top level definitional forms include `module'(object, theory), ~%-- `view', and `make'")
         (format t "~&  ?~20Tprint out this help")
         (format t "~&  quit -or-")
         (format t "~&  q~20Texit from CafeOBJ interpreter")
         (format t "~&  select <Modexp> ~20Tset the <Modexp> current")
         (format t "~&  show -or-")
         (format t "~&  describe~20Tprint various info., for further help, type `show ?'")
         (format t "~&-- setting switches:")
         (format t "~&  set~20Tset toplevel switches, for further help: type `set ?'")
         (format t "~&  protect <Modexp>~20Tprevent module from redefinition")
         (format t "~&  unprotect <Modexp>~20T un-set protection of module")
         (format t "~&-- simple semantic tools:")
         (format t "~&  check <things>~20Tcheck some properties of moudle,")
         (format t "~&  ~20Tfor further help, type `check ?'")
         (format t "~&  regularize <Modexp>~20T make the signature of <Modexp> regular")
         (format t "~&-- term rewriting commands:")
         (format t "~&  reduce -or- ")
         (format t "~&  red [in <Modexp> : ] <term> .")
         (format t "~&  ~20Trewrite <term> using equations as rewerite rules")
         (format t "~&  ~20Toptional <Modexp> specifies the context")
         (format t "~&  exec [in <Modexp> : ] <term> .")
         ;; (format t "~&  exec+ [in <Modexp> : ] <term> .")
         (format t "~&  ~20Trewrite <term> using both equations and rules")
         (format t "~&  ~20Toptional <Modexp> specifies the context")
         (format t "~&  parse [in <Modexp> : ] <term> .")
         (format t "~&  ~20Tparse <term>, print out the result")
         ;; (format t "~&  test {reduction|execution} <term> :expect <term> . ")
         ;; (format t "~&  ~20Tdo test reduction(execution) in the current context")
         ;; (format t "~&  rew limit {<number>| .}")
         ;; (format t "~&  ~20Tset(unset) max number of rewriting")
         ;; (format t "~&  stop at [<term>] .")
         ;; (format t "~&  ~20Tset(unset) stop pattern")
         (format t "~&-- theorem proving stuffs:")
         (format t "~&  apply~20Tapply rewrite rules to a term,~%~20Tfor further help: type `apply ?'")
         (format t "~&  start <term>~20Tset the term <term> as the target of \"apply\" command")
         (format t "~&  open {<Modexp> | .}~20T open module")
         (format t "~&  close ~20Tclose openning module")
         (format t "~&-- reading in files:")
         (format t "~&  input -or-")
         (format t "~&  in <file>~20Tread in <file>")
         (format t "~&  require <feature> [<file>]")
         (format t "~&  ~20Trequire <feature>")
         (format t "~&  provide <feature>~20Tprovide the <feature>")
         (format t "~&-- save/restore module definitions:")
         (format t "~&  save <file>~20Tsave current definitions of modules to <file>")
         (format t "~&  restore <file>~20Trestore definitions of modules from <file>")
         (format t "~&  reset ~20Trecover defintions of built-in modules and standard prelude")
         (format t "~&  full reset~20Treset system to initial status")
         (format t "~&-- misc. commands")
         (format t "~&  clean memo ~20T clean up term memoization table")
         (format t "~&  dribble {<file>| .}~20T if <file> is given, begins to record the interaction")
         (format t "~&  ~20Tto the specified file, else ends the recording.")
         (format t "~&  cd <directory>~20Tchange current directory")
         (format t "~&  ls <directory>~20Tlist files in directory")
         (format t "~&  pwd~20Tprint current directory")
         (format t "~&  lisp -or-")
         (format t "~&  lispq <lisp>~20Tevaluate lisp expression <lisp>")
         (format t "~&  ! <command>~20Tfork shell <command> (Unix only)"))
        (t (cafeobj-what-is com))))

;;; 
(defparameter .?-invalid-chars. '("." "#" "'" "`"))

#||
(defun cafeobj-what-is (inp)
  (flet ((check-pat (pat)
           (if (not (some #'(lambda (str)
                              (member str .?-invalid-chars. :test #'string=))
                          pat))
               t
             (progn (format *error-output*
                            "Illegal command/switch pattern: ~{~a ~^~}" pat)
                    nil))))
    (let* ((id (if (cddr inp)
                   (and (check-pat (cdr inp))
                        (mapcar #'read-from-string (cdr inp)))
                 (and (cadr inp)
                      (check-pat (cdr inp))
                      (read-from-string (cadr inp)))))
           (desc (if (keywordp id)
                     (get-msg-description id)
                   (and id (get-command-description (car inp) id)))))
      (unless id
        (format t "~&Usage: {? | ??} {<command/switch name or pattern> | <message ID>}")
        (return-from cafeobj-what-is nil))
      (if desc
          (format t desc)
        (format t "~&Unknown command/switch or message ID: ~{~a ~^~}." (cdr inp))))))
||#

(defun cafeobj-what-is (inp)
  (let* ((ask (intern (car inp)))
	 (question (cdr inp))
	 (key (reduce #'(lambda (x y) (concatenate 'string x y)) question))
	 (description nil))
    (case ask
      (|?| (setq description (get-document-string key)))
      ;; (|??| (setq description (get-detailed-document key)))
      ;; ((|?ex| |?example|) (setq description (get-example key)))
      (otherwise
       ;; this cannot happen
       (with-output-chaos-error ('internal-error)
	 (format t "Unknown help command ~a" (car inp)))))
    (cond (description (format t description)
		       (terpri))
	  (t (with-output-chaos-warning ()
	       (format t "System does not know about \"~{~a ~^~}\"." question))))))

;;; 
(defun get-command-description (level id)
  (if (string= level "??")
      (get-description id t)
    (get-description id nil)))

;;; READING IN FILES
;;;_____________________________________________________________________________

;;; CAFEOBJ-INPUT
;;;
(defun cafeobj-input (f &optional
                        (proc 'process-cafeobj-input)
                        (load-path *chaos-libpath*))
  (with-chaos-top-error ()
    (with-chaos-error ()
      (if *cafeobj-batch*
          (let ((*print-case* :downcase)
                #+CMU (common-lisp:*compile-verbose* nil)
                #+CMU (common-lisp:*compile-print* nil)
                #+CMU (ext:*gc-verbose* nil))
            (chaos-input-file :file f :proc proc :load-path load-path
                              :suffix '(".cafe" ".mod")))
        (chaos-input-file :file f :proc proc :load-path load-path
                          :suffix '(".cafe" ".mod"))))))

;;; CAFEOBJ-PROBE-FILE file
;;;
(defun cafeobj-probe-file (f)
  (let ((src (chaos-probe-file f *chaos-libpath* '(".cafe" ".mod")))
        (bin (chaos-probe-file f *chaos-libpath* '(".bin"))))
    (if (null bin)
        src
      (if src
          (if (<= (file-write-date src) (file-write-date bin))
              bin
            src)
        bin))))

;;; PROMPT
;;;_____________________________________________________________________________

;;; PRINT-CAFEOBJ-PROMPT
;;;

(defun print-cafeobj-prompt ()
  (fresh-all)
  (flush-all)
  (cond ((eq *prompt* 'system)
         (if *last-module*
             (if (module-is-inconsistent *last-module*)
                 (progn
                   (with-output-chaos-warning ()
                     (format t "~a is inconsistent due to changes in some of its submodules."
                             (module-name *last-module*))
                     (print-next)
                     (princ "resetting the `current module' of the system.."))
                   (setq *last-module* nil)
                   (format *error-output* "~&CafeOBJ> ")
                   )
               (let ((*standard-output* *error-output*))
                 (print-simple-mod-name *last-module*)
                 (princ "> ")))
           (format *error-output* "CafeOBJ> "))
         (setf *sub-prompt* nil))
        ((eq *prompt* 'none))
        (*prompt*
         (let ((*standard-output* *error-output*))
           (if (atom *prompt*)
               (princ *prompt*)
             (print-simple-princ-open *prompt*))
           (princ " "))))
  (flush-all))

;;; SAVE INTERPRETER IMAGE
;;;_____________________________________________________________________________
(defun set-cafeobj-libpath (topdir)
  (setq *system-prelude-dir*
    (concatenate 'string topdir "/prelude"))
  (setq *system-lib-dir*
    (concatenate 'string topdir "/lib"))
  (setq *system-ex-dir*
    (concatenate 'string topdir "/exs"))
  (setq *chaos-libpath* (list *system-lib-dir* *system-ex-dir*)))

#-(or (and CCL (not :openmcl)) ALLEGRO)
(defun set-cafeobj-standard-library-path (&optional topdir)
  (when (and (null *cafeobj-install-dir*)
             (null topdir))
    (break "CafeOBJ install directory is not set yet!."))
  (set-cafeobj-libpath (or topdir *cafeobj-install-dir*)))

#+:openmcl
(defun set-cafeobj-standard-library-path (&optional topdir)
  (when (and (null *cafeobj-install-dir*)
             (null topdir))
    (break "CafeOBJ install directory is not set yet!."))
  (set-cafeobj-libpath (or topdir *cafeobj-install-dir*)))

;;; ACL
#+:allegro
(defvar cafeobj-sys-dir nil)
#+:allegro
(defun set-cafeobj-standard-library-path (&optional topdir)
  (if topdir
      (set-cafeobj-libpath topdir)
    (progn
      (setq cafeobj-sys-dir 
        #+:mswindows (translate-logical-pathname #p"sys:")
        #-:mswindows (translate-logical-pathname
                      (merge-pathnames #p"sys:" #p"..")))
      (setq *cafeobj-install-dir* cafeobj-sys-dir)
      (setq *system-prelude-dir*
        (namestring (merge-pathnames *cafeobj-install-dir*
                                     "prelude")))
      (setq *system-lib-dir*
        (namestring (merge-pathnames *cafeobj-install-dir*
                                     "lib")))
      (setq *system-ex-dir*
        (namestring (merge-pathnames *cafeobj-install-dir*
                                     "exs")))
      (setq *chaos-libpath*
        (list *system-lib-dir* *system-ex-dir*)))))

;;; patch by t-seino@jaist.ac.jp
#+(and CCL (not :openmcl))
(defun set-cafeobj-standard-library-path (&optional topdir)
  (declare (ignore topdir))
  ;; (unless *cafeobj-install-dir*
  ;;    (break "CafeOBJ install directory is not set yet!."))
  (setq *system-prelude-dir*
    (full-pathname (make-pathname :host "ccl" :directory "prelude")))
  (setq *system-lib-dir*
    (full-pathname (make-pathname :host "ccl" :directory "lib")))
  (setq *system-ex-dir*
    (full-pathname (make-pathname :host "ccl" :directory "exs")))
  (setq *chaos-libpath* (list *system-lib-dir* *system-ex-dir*)))

;;; MAIN ROUTINE
;;; PROCESSING INPUT FILE STREAM
;;;_____________________________________________________________________________

;;; PROCESS-CAFEOBJ-INPUT
;;; read in command & process it until eof.
;;;
;;; cafeobj-parse returns the input in a form of list of tokens.
;;;  ("token", ... )
;;; the first token is always assumed to be a keyword, and the rest is
;;; its arguments. the form of arguments are depends on the syntax of
;;; each command. 
;;;

(defun bye-bye-bye ()
  #+GCL (bye)
  #+sbcl (sb-ext:exit)
  #+CMU (ext:quit)
  #+EXCL (exit)
  #+CCL (quit)
  #+CLISP (ext::exit))

;;;
;;; NOP
;;;
(defun cafeobj-nop (&rest ignore)
  ignore)

;;;
;;; cafeobj-evaluate-command : Key -> Void
;;;
(defun cafeobj-evaluate-command (key inp)
  (declare (type string key))
  (let ((com (get-command-info key)))
    (unless com
      (with-output-chaos-error ('no-commands)
	(format t "No such command or declaration keyword '~a'." key)))
    (let ((parser (comde-parser com)))
      (unless parser
	(with-output-chaos-error ('no-parser)
	  (format t "No parser is defined for command ~a" key)))
      (let ((pform (funcall parser inp)))
	(unless pform
	  (with-output-chaos-error ('parse-error)
	    (format t "Invalid argument to command ~a." key)))
	(if (eq pform :help)
	    (print-comde-usage com)
	  (let ((evaluator (comde-evaluator com)))
	    (unless evaluator
	      (with-output-chaos-error ('no-evaluator)
		(format t "No evaluator is defined for command ~a." key)))
	    (funcall evaluator pform)))))))

;;;
;;;
(defun parse-cafeobj-input-from-string (string)
  (let ((.reader-ch. 'space)
	(*reader-input* *reader-void*)
	(*print-array* nil)
	(*print-circle* nil)
	(*old-context* nil)
	(*show-mode* :cafeobj))
    (let ((inp nil)
	  (.in-in. nil))
      (declare (special .in-in.))
      (with-chaos-top-error ('handle-cafeobj-top-error)
	(with-chaos-error ('handle-chaos-error)
	  (setq inp (cafeobj-parse-from-string string))
	  (block process-input
	    ;; PROCESS INPUT
	    (cafeobj-evaluate-command (car inp) inp)))))))
;;;
;;; READING IN DECLARATIONS/COMMANDS and PROCESS THEM.
;;;
(defvar *on-top-debug* nil)

(defun process-cafeobj-input ()
  (let ((.reader-ch. 'space)
        (*reader-input* *reader-void*)
        (*print-array* nil)
        (*print-circle* nil)
        (*old-context* nil)
        (*show-mode* :cafeobj)
        (top-level (at-top-level)))
    (unless (or top-level *chaos-quiet*)
      (if *chaos-input-source*
          (with-output-simple-msg ()
            (format t "~&processing input : ~a~%" (namestring *chaos-input-source*)))
        (with-output-simple-msg ()
          (format t "~&processing input .......................~%"))))
    (let ((inp nil)
          (.in-in. nil))
      (declare (special .in-in.))
      (block top-loop
        (loop
          (with-chaos-top-error ('handle-cafeobj-top-error)
            (with-chaos-error ('handle-chaos-error)
              (when top-level
                (print-cafeobj-prompt))
              (setq inp (cafeobj-parse))

              ;; QUIT -----------------------------------------------------------
              (when (member (car inp) '("eof" "q" ":q" ":quit" "quit" eof) :test #'equal)
                ;; we should recover context here? NOOP! ...
                (return-from top-loop nil))

              (block process-input
                ;; PROCESS INPUT COMMANDS ==============
		(cafeobj-evaluate-command (car inp) inp))
              (setq *chaos-print-errors* t)))
          (when .in-in.
            (setq *chaos-print-errors* t)
            (setq .in-in. nil)))))))

(defun try-reduce-term (inp)
  (perform-reduction* inp *current-module* nil nil))

(defun handle-cafeobj-top-error (val)
  (if *chaos-input-source*
      (chaos-to-top val)
    val))

;;; EOF

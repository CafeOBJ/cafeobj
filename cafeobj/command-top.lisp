;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
#|==============================================================================
                            System: CHAOS
                           Module: cafeobj
                         File: command-top.lisp
==============================================================================|#
;;;
;;; Copyright (c) 2000-2014, Toshimi Sawada. All rights reserved.
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
                            (("-h" "-help" "--help")
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
                (format t "~%-- loading prelude")
                ;;(format t "~&-- do `save-system' for creating system prelude pre-loaded.")
                (setq *cafeobj-standard-prelude-path*
                  (load-prelude *cafeobj-initial-prelude-file* 'process-cafeobj-input)))
            (unless *cafeobj-standard-prelude-path*
              (format t "~%-- loading standard prelude")
              ;;(format t "~&-- do `save-system' for creating system prelude pre-loaded.")
              (setq *cafeobj-standard-prelude-path*
                (load-prelude "std" 'process-cafeobj-input))))
          (when *cafeobj-secondary-prelude-file*
            (format t "~%-- appending prelude")
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
(defun print-context-info ()
  (let ((cmod (get-context-module t)))
    (cond ((null cmod)
           (format t "~&You are at top level, no context module is set."))
          (*open-module*
           (format t "~&A module ~a is open. " (get-module-print-name *open-module*))
           (format t "In addition to toplevel commands,~%you can put any declarations of module constructs.~%")
           (format t "Try typing '?com element' for the list of available constructs."))
          (t
           (format t "~&Module ~a is set as current module." (get-module-print-name cmod))))))

(defun print-help-help ()
  (format t "~2%** Here are commands for CafeOBJ online help system.~%")
  (format t "'?com [<class>]'~25T Shows available commands classified by <class>,~%")
  (format t "~25T ommiting <classy> shows a list of <class>.~%")
  (format t "'? <name>'~25T Gives the reference manual description of <name>~%")
  (format t "'?ex <name>'~25T Similar to '? <name>', but in this case~%")
  (format t "~25T also shows examples if available.~%")
  (format t "'?ap <term> [<term>] ...'~25TSearches all available online docs for the terms passed,~%")
  (format t "~25T type '? ?ap' for more detailed descriptions.~%")
  (format t "** Typing 'com' will show the list of major toplevel commands.~%")
  (format t "** URL 'http://cafeobj.org' privides anything you want to know about CafeOBJ."))

(defun cafeobj-top-level-help (&optional com)
  (cond ((null (cdr com))
         (let ((ask (intern (car com))))
           (case ask
             ((|?com| |?commands|) (oldoc-list-categories nil))
             (otherwise (print-context-info)
                        (print-help-help)))))
        (t (cafeobj-what-is com))))

(defparameter .cafeobj-main-commands.
"-- CafeOBJ major top level commands:
   NOTE: Top level definitional forms include declaration of `module' and `view'.
-- help:
   ?                   shows the current context and the brief guide for using help system.
-- exit:
   quit -or- q         exit from CafeOBJ interpreter.
-- setting working context:
   select <Modexp> .   set the module specified by a module expression <Modexp> as current module.
   open <Modexp> .     open the module specified by a module expression <Moexp>,
                       <Modexp> will be a current module.
   close               close the opening module.
-- term rewriting commands:
   reduce -or-
   red [in <Modexp> : ] <term> . 
                       rewrite <term> using equations as rewerite rules
                       optional <Modexp> specifies the rewriting context (module)
   exec [in <Modexp> : ] <term> .
                       rewrite <term> using both equations and rules
                       optional <Modexp> specifies the rewriting context (module)
-- term parser:
  parse [in <Modexp> : ] <term> . 
                       parse <term>, print out the result
                       optional <Modexp> specfies the parsing context (module)
-- inspection:
   show -or- describe  print various info., for further help, type `show ?'
-- setting switches:
   set                 set toplevel switches, for further help: type `set ?'
   protect <Modexp>    prevent module <Modexp> from redefinition
   unprotect <Modexp>  un-set protection of module <Modexp>
-- reading in files:
  input -or-
  in <pathname>        requests the system to read the file specified by the pathname. 
                       The file itself may contain 'input' commands.
-- system intialization
  reset                restores the definitions of built-in modules and preludes,  
                       but does not affect other modules.
  full reset           reinitializes the internal state of the system. 
                       all supplied modules definitions are lost.
-- misc. commands
  cd <directory>       change the system's working directory
  ls <directory>       list files in directory
  pwd                  print the current directory
  ! <command>          fork shell <command> (Unix only)"
)

(defun show-cafeobj-main-commands ()
  (format t "~a~%" .cafeobj-main-commands.))

;;; 
(defparameter .?-invalid-chars. '("." "#" "'" "`"))

(defun cafeobj-what-is (inp)
  (let* ((ask (intern (car inp)))
         (question (cdr inp))
         (description nil))
    (case ask
      (|?| (setq description (oldoc-get-documentation question :main t :example nil)))
      (|??| (setq description (oldoc-get-documentation question :main t :example t)))
      ((|?ex| |?example|) (setq description (oldoc-get-documentation question :main nil :example t)))
      ((|?ap| |?apropos|) (setq description (oldoc-get-documentation question :apropos t)))
      ((|?com| |?command|) (oldoc-list-categories question)
                            (return-from cafeobj-what-is nil))
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
  (let ((cur-module (get-context-module t)))
    (cond ((eq *prompt* 'system)
           (if cur-module
             (if (module-is-inconsistent cur-module)
                 (progn
                   (with-output-chaos-warning ()
                     (format t "~a is inconsistent due to changes in some of its submodules."
                             (module-name cur-module))
                     (print-next)
                     (princ "resetting the `current module' of the system.."))
                   (reset-context-module)
                   (format *error-output* "~&CafeOBJ> "))
               (let ((*standard-output* *error-output*))
                 (print-simple-mod-name cur-module)
                 (princ "> ")))
             ;; no context module
             (format *error-output* "CafeOBJ> "))
           (setf *sub-prompt* nil))
          ;; prompt specified to NONE
          ((eq *prompt* 'none))
          ;; specified prompt
          (*prompt*
           (let ((*standard-output* *error-output*))
             (if (atom *prompt*)
                 (princ *prompt*)
               (print-simple-princ-open *prompt*))
             (princ " "))))
    (flush-all)))

;;; SAVE INTERPRETER IMAGE
;;;_____________________________________________________________________________
(defun set-cafeobj-libpath (topdir)
  (setq *system-prelude-dir*
    (pathname (concatenate 'string topdir "/prelude/")))
  (setq *system-lib-dir*
    (pathname (concatenate 'string topdir "/lib/")))
  (setq *system-ex-dir*
    (pathname (concatenate 'string topdir "/exs/")))
  ;; (setq *chaos-libpath* (list *system-lib-dir* *system-ex-dir*))
  (setq *chaos-libpath* (list *system-lib-dir*)))

#-(or (and CCL (not :openmcl)) ALLEGRO (and SBCL WIN32))
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
    (let ((*default-pathname-defaults* #p"sys:"))
      #-:mswindows (setq *default-pathname-defaults* (merge-pathnames #p"../"))
      (setq *cafeobj-install-dir* (translate-logical-pathname *default-pathname-defaults*))
      (setq *system-prelude-dir* (translate-logical-pathname (merge-pathnames "prelude/")))
      (setq *system-lib-dir* (translate-logical-pathname (merge-pathnames "lib/")))
      (setq *system-ex-dir* (translate-logical-pathname (merge-pathnames "exs/")))
      ;;; (setq *chaos-libpath* (list *system-lib-dir* *system-ex-dir*))
      (setq *chaos-libpath* (list *system-lib-dir*)))))

#+(and :SBCL :win32)
(defun set-cafeobj-standard-library-path (&optional topdir)
  (if topdir
      (set-cafeobj-libpath topdir)
    (let* ((*default-pathname-defaults* (make-pathname :host (pathname-host sb-ext:*core-pathname*)
                                                       :device (pathname-device sb-ext:*core-pathname*)
                                                       :directory (pathname-directory sb-ext:*core-pathname*))))
      (setq *cafeobj-install-dir* *default-pathname-defaults*)
      (setq *system-prelude-dir* (translate-logical-pathname (merge-pathnames "prelude/")))
      (setq *system-lib-dir* (translate-logical-pathname (merge-pathnames "lib/")))
      (setq *system-ex-dir* (translate-logical-pathname (merge-pathnames "exs/")))
      ;;; (setq *chaos-libpath* (list *system-lib-dir* *system-ex-dir*))
      (setq *chaos-libpath* (list *system-lib-dir*)))))

;;; patch by t-seino@jaist.ac.jp
#+(and CCL (not :openmcl))
(defun set-cafeobj-standard-library-path (&optional topdir)
  (declare (ignore topdir))
  ;; (unless *cafeobj-install-dir*
  ;;    (break "CafeOBJ install directory is not set yet!."))
  (setq *system-prelude-dir*
    (full-pathname (make-pathname :host "ccl" :directory "prelude/")))
  (setq *system-lib-dir*
    (full-pathname (make-pathname :host "ccl" :directory "lib/")))
  (setq *system-ex-dir*
    (full-pathname (make-pathname :host "ccl" :directory "exs/")))
  ;; (setq *chaos-libpath* (list *system-lib-dir* *system-ex-dir*))
  (setq *chaos-libpath* (list *system-lib-dir*)))

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

(defun handle-cafeobj-top-error (val)
  (if *chaos-input-source*
      (chaos-to-top val)
    val))

;;; EOF

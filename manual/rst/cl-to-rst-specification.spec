
Specification for a Lisp to RST conversion
==========================================

Every line starting with
	;d;
is consider "documentation input"

The documentation generation routine has the concept of
current output file. By default it is the name of the
input file currently read. I.e., if the file
	foo.cl
is converted the default output file is named
	foo.rst
The documentation conversion strips the last extension
(only 1) and adds rst. In case there is already a file
named like that, the translation process stops.

If the first character after the ";d;" of a documentation
line is a <SPACE>, i.e., the input line starts with
	;d;<SPACE>
where <SPACE> is a literal space, then everything
following the <SPACE> is written into the current 
output file.

If the first char after the ";d;" is an "=", then
some directives for the translation mechanism 
can follow. Current directives are:
	;d;=file=<outputfile>
	  changes the current output file
	;d;=priority=<NN>
	  gives the following block a priority of NN
	;d;=sortstring=<STRING>
	  gives a sort string within this priority

Output process:
- all file given on the command line are read
- blocks with the same output file but different
  priority are written in increasing priority
  sequence.
- blocks within the same priority are sorted 
  according to the sortstring directive
  all blocks without sortstring added at the end
- all block without specified priority get value 500

----------------------

This allows to combine function/syntax definitions
from various input files into one documentation file

Example: (from file cafeobj/cafeobj-top.lisp)


;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: cafeobj-top.lisp,v 1.3 2007-01-18 11:03:38 sawada Exp $

;d;=file=toplevel.rst
;d; 
;d; The CafeOBJ Top Level
;d; =====================
;d;
;d; The CafeOBJ top level defines the following functions ...
;d;

....

;d;=file=interface.rst
;dl=priority=20
;d; 
;d; CafeOBJ greets the user with a variety of information
;d; on the underlying lisp interpreter, the time it was build
;d; etc etc

(defun cafeobj-greeting ()
  ;; (declare (values t))
  (unless (or *cafeobj-batch* *cafeobj-no-banner*)
    (let ((*print-pretty* nil))
      ;;(declare (special *print-pretty*))
      (fresh-line)
      (terpri)
      (print-centering g_line_1)
      (fresh-line)
      (print-centering (format nil " built: ~a" 
                               (if -cafeobj-load-time-
                                   -cafeobj-load-time-
                                 "not yet installed.")))
      (fresh-line)
      (print-centering
       (format nil "prelude file: ~a"
               (if *cafeobj-standard-prelude-path*
                   (file-namestring *cafeobj-standard-prelude-path*)
                 'NONE)))
      (fresh-line)
      (print-centering "***")
      (fresh-line)
      (print-centering (get-time-string))
      (fresh-line)
      (print-centering "Type ? for help")
      (fresh-line)
      (force-output))))

(defvar .lisp-implementation. (lisp-implementation-type))
(defvar .lisp-version. (lisp-implementation-version))

(defun sub-message ()
  (let ((*print-pretty* nil))
    (declare (special *pint-pretty*))
    #+:BigPink
    (unless (or *cafeobj-batch* *cafeobj-no-banner*)
      (print-centering "***")
      (fresh-line)
      (print-centering "-- Containing PigNose Extensions --")
      (fresh-line)
      )
    (unless *cafeobj-batch*
      (print-centering "---")
      (fresh-line)
      (print-centering (concatenate
                           'string "built on " .lisp-implementation.))
      (fresh-line)
      (print-centering .lisp-version.))))

;;;=============================================================================
;;; The top level loop
;;;=============================================================================
;;; TOP LEVEL FUNCTION

#-microsoft
(defun cafeobj (&optional no-init)
  (cafeobj-init)
  (unless no-init
    (cafeobj-process-args)
    nil)
  ;; greeting message
  (cafeobj-greeting)
  ;;
  (sub-message)
  ;;
  (catch *top-level-tag*
    (with-chaos-top-error ()
      (with-chaos-error ()
        (dolist (f (reverse *cafeobj-initial-load-files*))
          (cafeobj-input f)))))
  ;;
  (if (not *cafeobj-batch*)
      (progn
        ;;
        (let ((quit-flag nil)
              (*print-case* :downcase)
              #+CMU (common-lisp:*compile-verbose* nil)
              #+CMU (common-lisp:*compile-print* nil)
              #+CMU (ext:*gc-verbose* nil)
              #+:ALLEGRO (*global-gc-behavior* :auto)
              #+:ALLEGRO (*print-pretty* nil)
              )
          #+:ALLEGRO
          (declare (special *global-gc-behaviour* *print-pretty*))
          (unless no-init
            (catch *top-level-tag*
              (with-chaos-top-error ()
                (with-chaos-error ()
                  (cafeobj-init-files)))))
          (loop (catch *top-level-tag*
                  (process-cafeobj-input)
                  (setq quit-flag t))
            (when quit-flag (return))))
        (format t "[Leaving CafeOBJ]~%")))
  (finish-output))

#+microsoft
(defun cafeobj (&optional no-init)
  (let ((*terminal-io* *terminal-io*)
        (*standard-input* *terminal-io*)
        (*standard-output* *terminal-io*)
        #+:ALLEGRO (*print-pretty* nil))
    (declare (special *print-pretty*))
    ;;
    (cafeobj-init)
    (unless no-init
      (cafeobj-process-args)
      nil)
    ;; greeting message
    (cafeobj-greeting)
    ;;
    (sub-message)
    ;;
    (catch *top-level-tag*
      (with-chaos-top-error ()
        (with-chaos-error ()
          (dolist (f (reverse *cafeobj-initial-load-files*))
            (cafeobj-input f)))))
    ;;
    (if (not *cafeobj-batch*)
        (progn
          ;;
          (let ((quit-flag nil)
                (*print-case* :downcase)
                (*global-gc-behavior* :auto)
                )
            (declare (special *global-gc-behaviour*))
            (unless no-init
              (catch *top-level-tag*
                (with-chaos-top-error ()
                  (with-chaos-error ()
                    (cafeobj-init-files)))))
            (loop (catch *top-level-tag*
                    (process-cafeobj-input)
                    (setq quit-flag t))
              (when quit-flag (return)))
            )
          (format t "[Leaving CafeOBJ]~%")))
    (finish-output) 
    ))

;;;=============================================================================
;;; MISC TOPLEVEL SUPPORT ROUTINES
;;;-----------------------------------------------------------------------------

(defun cafeobj-init ()
  ;; #+gcl
  ;; (si::allocate-relocatable-pages 1000 t)
  #+CMU
  (unix:unix-sigsetmask 0)
  #+:ALLEGRO
  (setq excl:*print-startup-message* nil)
  #+:ALLEGRO
  (setf (sys:gsgc-switch :print) nil)
  ;;
  (!lex-read-init)
  (chaos-initialize-fsys))

;;; initialization at startup time.
;;;-----------------------------------------------------------------------------
(defun cafeobj-init-files ()
  (when *cafeobj-load-init-file*
    (when *chaos-vergine*
      (let ((val (get-environment-variable "CAFEOBJINIT")))
        (if (and val (probe-file val))
            (cafeobj-input val)
          (if (probe-file (make-pathname :name ".cafeobj"))
              (cafeobj-input (make-pathname :name ".cafeobj"))
            (let ((home (or 
                         (namestring (user-homedir-pathname))
                         (get-environment-variable "HOME")
                         )))
              (when home
                (let ((dot-cafeobj (merge-pathnames
                                    home
                                    (make-pathname :name ".cafeobj"))))
                  (when (probe-file dot-cafeobj)
                    (cafeobj-input dot-cafeobj))))))))
      (let ((lib-path (get-environment-variable "CAFEOBJLIB"))
            (load-path nil))
        (when lib-path
          (dolist (x (parse-with-delimiter lib-path #\:))
            (push x load-path))
          (setq *chaos-libpath* (append (nreverse load-path)
                                        *chaos-libpath*))
          ))
      (setq *chaos-vergine* nil)))
  ;; message DB
  #+:Allegro
  (setup-message-db)
  ;; help DB
  #+:Allegro
  (setup-help-db)
  )

;;; **********************
;;; THE TOP LEVEL FUNCTION
;;; **********************

(defmacro abort-on-error (&body forms)
  `(handler-bind ((error #'abort))
     ,@forms))

(defun cafeobj-top-level ()
  ;; dirty kludge!!
  (setq *print-pretty* nil)
  #+GCL
  (progn
    (si::set-up-top-level)
    (setq si::*ihs-top* 1)
    (incf system::*ihs-top* 2))
  ;;
  (in-package :chaos)
  ;; patch by t-seino@jaist.ac.jp
  #+(or CCL allegro)
  (set-cafeobj-standard-library-path)
  ;;
  (with-simple-restart (abort "Sorry... we must abort.")
    (let ((res (catch *top-level-tag* (cafeobj) 'ok-exit)))
      (if (eq res 'ok-exit)
	  (bye-bye-bye)
	(progn
	  (princ "** ERROR")
	  (terpri)))))
  )

#+EXCL
(eval-when (:execute :load-toplevel)
  (top-level:alias "q" (&rest args)
    (apply #'top-level:do-command "pop" args)))

;; EOF

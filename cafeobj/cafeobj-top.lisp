;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: cafeobj-top.lisp,v 1.3 2007-01-18 11:03:38 sawada Exp $
(in-package :chaos)
#|==============================================================================
                             System: CHAOS
                            Module: cafeobj
                            File: top.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;;*****************************************************************************
;;;                CafeOBJ Top Level
;;;*****************************************************************************

;;;=============================================================================
;;; Control Flags & Values for top level.
;;;=============================================================================

(defvar g_line_1 (format nil "-- CafeOBJ system Version ~a --" cafeobj-version))

(eval-when (eval load)
  (setq -cafeobj-load-time- (chaos::get-time-string)))

(defun cafeobj-greeting ()
  ;; (declare (values t))
  (unless (or *cafeobj-batch* *cafeobj-no-banner*)
    (let ((*print-pretty* nil))
      (declare (special *print-pretty*))
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
  (let ((res (catch *top-level-tag* (cafeobj) 'ok-exit)))
    (if (eq res 'ok-exit)
        (bye-bye-bye)
      (progn
        (princ "** ERROR")
        (terpri)))))

#+EXCL
(eval-when (eval load)
  (top-level:alias "q" (&rest args)
    (apply #'top-level:do-command "pop" args)))

;; EOF

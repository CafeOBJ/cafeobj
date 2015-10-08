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

(eval-when (:execute :load-toplevel)
  (setq -cafeobj-load-time- (chaos::get-time-string)))

(defun cafeobj-greeting ()
  (unless (or *cafeobj-batch* *cafeobj-no-banner*)
    (let ((*print-pretty* nil))
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
    (unless (or *cafeobj-batch* *cafeobj-no-banner*)
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
          (with-simple-restart (nil "Exit CafeOBJ.")
            (loop
              (with-simple-restart (abort "Return to CafeOBJ Top level.")
                (catch *top-level-tag*
                  (process-cafeobj-input)
                  (setq quit-flag t))
                (when quit-flag (return :ok-exit))))))
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
            (with-simple-restart (nil "Exit CafeOBJ.")
              (loop
                (with-simple-restart (abort "Return to CafeOBJ Top level.")
                  (catch *top-level-tag*
                    (process-cafeobj-input)
                    (setq quit-flag t))
                  (when quit-flag (return :ok-exit))))))
          (format t "[Leaving CafeOBJ]~%")))
    (finish-output) ))

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
    (when *chaos-new*
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
      (setq *chaos-new* nil)))
  ;; message DB
  ;; #+:Allegro
  ;; (setup-message-db)
  ;; help DB
  ;; #+:Allegro
  ;; (setup-help-db)
  )

;;; **********************
;;; THE TOP LEVEL FUNCTION
;;; **********************

(defmacro abort-on-error (&body forms)
  `(handler-bind ((error #'abort))
     ,@forms))

(defun resume-cafeobj (&rest ignore)
  (declare (ignore ignore))
  (throw *top-level-tag* nil))

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
  #+(or CCL allegro (and SBCL win32))
  (set-cafeobj-standard-library-path)
  ;;
  (let ((res (catch *top-level-tag* (cafeobj) 'ok-exit)))
    (if (eq res 'ok-exit)
        (bye-bye-bye)
      (progn
        (princ "** ERROR")
        (terpri)))))

#+EXCL
(eval-when (:execute :load-toplevel)
  (top-level:alias "q" (&rest args)
    (apply #'top-level:do-command "pop" args)))

;; EOF

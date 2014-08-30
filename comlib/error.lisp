;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
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
#|==============================================================================
				 System: CHAOS
				 Module: comlib
				File: error.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; *********************
;;; STANDRD ERROR HANDLER
;;; *********************

;;; - catches tag 'chaos-main-error
;;;
;;; << IMPORTANT ASSUMPTION >>
;;; - every chaos AST evaluators report errors by themselves
;;;   and then call 'chaos-error with non-nil value.
;;; << SHOULD >>
;;; - users should do anything with-in a body of `with-chaos-error' or
;;;   catch 'chaos-main-error by themselves.
;;;

(declaim (special *suppress-err-handler-msg*))
(defvar *suppress-err-handler-msg* nil)

;;; SIGNAL STANDRD ERROR
;;;
(defun chaos-error (err-value)
  (flush-all)
  (throw 'chaos-main-error err-value))

;;; HANDLER
;;;
(defun get-chaos-error-proc (val)
  (if (symbolp val)
      (get val ':chaos-error-handler)
      nil))

(defmacro with-chaos-error ((&optional error-proc) &body body)
  (if error-proc
      ` (let ((ret-val nil))
	  (let ((val (catch 'chaos-main-error
		       (setq ret-val
			     (progn ,@body))
		       nil)))
	    (if val
		(funcall ,error-proc val)
		ret-val)))
	` (let ((ret-val nil))
	    (let ((val (catch 'chaos-main-error
			 (setq ret-val
			       (progn ,@body))
			 nil)))
	      (if val
		  (let ((std-proc (get-chaos-error-proc val)))
		    (if std-proc
			(funcall std-proc val)
			(chaos-to-top)))
		  ret-val)))))
  
(defun chaos-indicate-position ()
  (unless *suppress-err-handler-msg*
    (when *chaos-input-source*		; nil means may be from terminal
      (format t "~&filename: ~a" (namestring *chaos-input-source*))
      (when (file-position *standard-input*)
	(format t " in top-level form ending at character position: ~d"
		(file-position *standard-input*)))
      (terpri))))

(defun chaos-to-top (&rest ignore)
  (declare (ignore ignore))
  (fresh-line)
  (chaos-indicate-position)
  (unless *suppress-err-handler-msg*
    (format t "~%** returning to top level~%"))
  (throw 'chaos-top-level-error t))

(defmacro with-chaos-top-error ((&optional error-proc) &body body)
  (if error-proc
      ` (let ((ret-val nil))
	  (let ((val (catch 'chaos-top-level-error
		       (setq ret-val
			     (progn ,@body))
		       nil)))
	    (if val
		(funcall ,error-proc val)
		ret-val)))
	` (let ((ret-val nil))
	    (let ((val (catch 'chaos-top-level-error
			 (setq ret-val
			       (progn ,@body))
			 nil)))
	      (if val
		  (let ((std-proc (get-chaos-error-proc val)))
		    (if std-proc
			(funcall std-proc val)
			;; we assume no more error handlers.
			nil))
		  ret-val)))))

(defmacro ignoring-chaos-error (&body body)
  ` (catch 'chaos-top-level-error
      (catch 'chaos-main-error
	,@body)))
;;; EOF

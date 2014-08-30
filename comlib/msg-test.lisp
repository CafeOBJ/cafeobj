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
;;; (in-package :chaos)
#|==============================================================================
				 System: CHAOS
				 Module: comlib
			       File: message.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

(defvar *Panic-messages* (make-hash-table))
(defvar *Error-messages* (make-hash-table))
(defvar *Warning-messages* (make-hash-table))
(defvar *Simple-messages* (make-hash-table))
(defvar *Messages* (make-hash-table))

(defun flush-all ()
  (finish-output *standard-output*)
  (finish-output *error-output*)
  )

(defun fresh-all ()
  (fresh-line *standard-output*)
  (fresh-line *error-output*))

(defun get-msg-fmt (type id)
  (case type 
    (:panic (gethash id *Panic-messages*))
    (:error (gethash id *Error-messages*))
    (:warning (gethash id *Warning-messages*))
    (:smessage (gethash id *Simple-messages*))
    (:message (gethash id *Messages*))
    (otherwise (error "Internal error: unknown message type ~a" type))
    ))

(defun output-msg (type id prefix &rest args)
  (apply #'format t (concatenate 'string prefix
                                 (get-msg-fmt type id))
         args))

(defmacro with-output-chaos-error-n ((msg-id args &optional (tag 'to-top tag-p)) &body body)
  ` (progn
      (let ((*standard-output* *error-output*)
            (*print-indent* 4))
        (output-msg :error ',msg-id "~&[Error]:" ,args)
        ,@body)
      ,(if (and tag-p (eq tag 'to-top))
           `(chaos-to-top)
         `(chaos-error ,tag)
         )))

(defmacro with-output-chaos-warning-n ((msg-id args) &body body)
  ` (unless *chaos-quiet*
      (let ((*standard-output* *error-output*)
            (*print-indent* 4)) 
        (output-msg :warning ',msg-id "~&[Warning]: " ,args)
        ,@body)
      (flush-all)))

(defmacro with-output-panic-message-n ((msg-id args) &body body)
  ` (progn
      (let ((*standard-output* *error-output*))
        (output-msg :panic ',msg-id "~&!! PANIC !!: " ,args)
        ,@body)
      (chaos-to-top)))
;;;
(defmacro with-output-msg-n ((msg-id args &optional (stream '*error-output*)) &body body)
  ` (unless *chaos-quiet*
      (let ((*standard-output* ,stream)
            (*print-indent* 3))
        (output-msg :message ',msg-id "~&-- " ,args)
        ,@body)
      (flush-all)))

(defmacro with-output-simple-msg-n ((msg-id args &optional (stream '*error-output*)) &body body)
  ` (unless *chaos-quiet*
      (let ((*standard-output* ,stream)
            (*print-indent* 2))
        (output-msg :smessage "~&" ',msg-id ,args)
        ,@body)
      (flush-all)))

;;;
(defun print-in-progress (str)
  (unless *chaos-quiet*
    (princ str *error-output*)
    (finish-output *error-output*)))

;;; I-miss-current-module me
;;; Checks if the *current-module* is bound, returns nil with an error mesage if
;;; *current-mdoule* is not bound to non-nil value.
;;; - me must a name (symbol) of a block.
;;;
(defmacro I-miss-current-module (me)
  ` (unless *current-module*
      (fresh-all)
      (flush-all)
      (with-output-panic-message (:p-no-module '(,me))
        ;; (format t "in ~a : no current module is specified!" ',me)
        (force-output)
        (finish-output)
        (return-from ,me nil))))

;;; EOF

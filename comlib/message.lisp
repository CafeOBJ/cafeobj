;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: message.lisp,v 1.3 2010-07-14 01:59:02 sawada Exp $
(in-package :chaos)
#|==============================================================================
				 System: CHAOS
				 Module: comlib
			       File: message.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

(defun flush-all ()
  (finish-output *standard-output*)
  (finish-output *error-output*)
  )

(defun fresh-all ()
  (fresh-line *standard-output*)
  (fresh-line *error-output*))

;;;
;;; Message DB
;;;
(defvar *Message-DB* (make-hash-table))

;;; 
(defun get-msg-type (id)
  (first (gethash id *Message-DB*)))
(defun get-msg-level (id)
  (second (gethash id *Message-DB*)))
(defun get-msg-fmt (id)
  (third (gethash id *Message-DB*)))
(defun get-msg-description (id)
  (fourth (gethash id *Message-DB*)))

(defun register-message (type msg)
  (setf (gethash (car msg) *Message-DB*) (cons type (cdr msg))))

#+:Allegro
(defun read-message-db (path)
  (clrhash *Message-DB*)
  (flet ((regme (type msgs)
           (dolist (msg msgs)
             (register-message type msg))))
    (with-open-file (strm path :if-does-not-exist :error
		     :external-format :utf-8)
      (loop for type = (read strm nil :eof)
          while (not (eq type :eof))
          do (case type
               ((:panic :panics) (regme :panic (read strm nil)))
               ((:error :errors) (regme :error (read strm nil)))
               ((:warning :warnings) (regme :warning (read strm nil)))
               ((:message :messages) (regme :message (read strm nil)))
               ((:smessage :smessages) (regme :smessage (read strm nil)))
               (otherwise
                (error "Internal error, invalid message type ~s" type)))))))

#+:Allegro
(defun setup-message-db ()
  (let ((fname (chaos-probe-file "messagesDB" *chaos-libpath* '(".msg"))))
    (unless fname
      (error "Internal error, can't find messagesDB."))
    (read-message-db fname)))

;;;
;;; OUTPUT-MSG
;;;

;;; message level
;;; 0 : always
;;; 1 : standard
;;; 2 : only under verbose mode
;;;
(defvar *msg-lvl* 1)
(defvar *old-msg-lvl* *msg-lvl*)

(defun set-verbose-lvl (lvl)
  (if (<= lvl 3)
      (setf *msg-lvl* lvl)
    (error "Internal error, invalid verbose level ~d" lvl)))

(defun set-verbose-on ()
  (setf *old-msg-lvl* *msg-lvl*)
  (set-verbose-lvl 0)
  (setq *chaos-verbose* t))

(defun set-verbose-off ()
  (when (zerop *msg-lvl*)
    (set-verbose-lvl *old-msg-lvl*))
  (setq *chaos-verbose* nil))

(defun set-expert-on ()
  (setf *old-msg-lvl* *msg-lvl*)
  (set-verbose-lvl 2))

(defun set-export-off ()
  (when (= *msg-lvl* 2)
    (set-verbose-lvl *old-msg-lvl*)))

(defun set-quiet-on ()
  (setf *old-msg-lvl* *msg-lvl*)
  (set-verbose-lvl 3))

(defun set-quiet-off ()
  (when (= *msg-lvl* 3)
    (set-verbose-lvl *old-msg-lvl*)))

(defun output-msg (id prefix args)
  (when (>= (get-msg-level id) *msg-lvl*)
    (apply #'format t (concatenate 'string
                        prefix
                        "(:"
                        (string id)
                        ") "
                        (get-msg-fmt id))
           args)))

(defmacro with-output-chaos-error-n ((msg-id args &optional (tag 'to-top tag-p)) &body body)
  ` (progn
      (let ((*standard-output* *error-output*)
            (*print-indent* 4))
        (output-msg ',msg-id "~&[Error]" ,args)
        ,@body)
      ,(if (and tag-p (eq tag 'to-top))
           `(chaos-to-top)
         `(chaos-error ,tag)
         )))

(defmacro with-output-chaos-warning-n ((msg-id args) &body body)
  ` (unless *chaos-quiet*
      (let ((*standard-output* *error-output*)
            (*print-indent* 4)) 
        (output-msg ',msg-id "~&[Warning]" ,args)
        ,@body)
      (flush-all)))

(defmacro with-output-panic-message-n ((msg-id args) &body body)
  ` (progn
      (let ((*standard-output* *error-output*))
        (output-msg ',msg-id "~&!! PANIC !!" ,args)
        ,@body)
      (chaos-to-top)))

(defmacro with-output-msg-n ((msg-id args &optional (stream '*error-output*)) &body body)
  ` (unless *chaos-quiet*
      (let ((*standard-output* ,stream)
            (*print-indent* 3))
        (output-msg ',msg-id "~&-- " ,args)
        ,@body)
      (flush-all)))

(defmacro with-output-simple-msg-n ((msg-id args &optional (stream '*error-output*)) &body body)
  ` (unless *chaos-quiet*
      (let ((*standard-output* ,stream)
            (*print-indent* 2))
        (output-msg ',msg-id "~&" ,args)
        ,@body)
      (flush-all)))

;;; older versions

(defmacro with-output-chaos-error ((&optional (tag 'to-top)) &body body)
  ` (progn
      ;; (flush-all)
      ;; (fresh-all)
      (let ((*standard-output* *error-output*)
	    (*print-indent* 4))
	(format t "~&[Error]: ")
	,@body)
      ,(if (eq tag 'to-top)
	   `(chaos-to-top)
	   `(chaos-error ,tag)
      )))

(defmacro with-output-chaos-warning ((&optional (stream '*error-output*)) &body body)
  ` (unless *chaos-quiet*
      ;; (fresh-all)
      ;; (flush-all)
      (let ((*standard-output* ,stream)
	    (*print-indent* 4)) 
	(format t "~&[Warning]: ")
	,@body)
      (flush-all)))

(defmacro with-output-panic-message ((&optional (stream '*error-output*)) &body body)
  ` (progn
      ;; (fresh-all)
      ;; (flush-all)
      (let ((*standard-output* ,stream))
	(print-next)
	(princ "!! PANIC !!: ")
	,@body)
      (chaos-to-top)))

;;;
(defmacro with-output-msg ((&optional (stream '*standard-output*)) &body body)
  ` (unless *chaos-quiet*
      ;; (fresh-all)
      ;; (flush-all)
      (let ((*standard-output* ,stream)
	    (*print-indent* 3))
	(format t "~&-- ")
	,@body)
      (flush-all)))

(defmacro with-output-simple-msg ((&optional (stream '*standard-output*)) &body body)
  ` (unless *chaos-quiet*
      ;; (fresh-all)
      ;; (flush-all)
      (let ((*standard-output* ,stream)
	    (*print-indent* 2))
	(format t "~&")
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
      (with-output-panic-message ()
	(format t "in ~a : no current module is specified!" ',me)
	(force-output)
	(finish-output)
	(return-from ,me nil))))

;;; EOF

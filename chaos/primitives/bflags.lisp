;;;-*-Mode:LISP; Package: CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: bflags.lisp,v 1.1 2007-02-07 06:35:57 sawada Exp $
;;;
(in-package :chaos)
#|=============================================================================
			     System:Chaos
		       Module:chaos/primitives
			   File:bflag.lisp
=============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;;
;;; generic chaos flag/parameter utils
;;;
(eval-when (:execute :compile-toplevel :load-toplevel)
(defstruct (chaos-flag (:type list)
	    (:conc-name "CFLG-"))
  (value nil :type t)
  (canon-name nil :type symbol)
  (name nil :type list)
  (hook #'identity :type function)
  (doc-string "" :type string)
  (group nil :type symbol))
)

(defvar *chaos-control-flags* (make-hash-table))
(defvar *chaos-flag-names* (make-hash-table :test #'equal))

(defun canonicalize-flag-name (name)
  (if (symbolp name)
      name				; assumes this is canonicalized name
    (or (gethash name *chaos-flag-names*)
	(with-output-chaos-error ('no-such-flag)
	  (format t "no such flag ~s." name)))))

(defmacro find-chaos-flag-or-error (name)
  `(let ((n (canonicalize-flag-name ,name)))
     (gethash n *chaos-control-flags*)))

;;; basic flag accessors
;;; name can be string (given name) or symbol (canonicalized one)
;;;
(defmacro chaos-flag (name)
  `(cflg-value (find-chaos-flag-or-error ,name)))
(defmacro chaos-flag-names (name)
  `(cflg-name (find-chaos-flag-or-error ,name)))
(defmacro chaos-flag-hook (name)
  `(cflg-hook (find-chaos-flag-or-error ,name)))
(defmacro chaos-flag-group (name)
  `(cflg-group (find-chaos-flag-or-error ,name)))
(defmacro chaos-flag-doc-string (name)
  `(cflg-doc-string (find-chaos-flag-or-error ,name)))

;;; 
(defun get-flag-group (group)
  (declare (type symbol group))
  (let ((flg nil))
    (maphash #'(lambda (x y)
		 (declare (ignore x))
		 (when (eq group (cflg-group y))
		   (push y flg)))
	     *chaos-control-flags*)
    flg))


;;; DECLARE-CHAOS-FLAG
;;;
(defmacro declare-chaos-flag (&key names
				   canon-name
				   initial-value
				   (doc-string "")
				   (group nil)
				   (hook #'identity))
  `(let ((flg (make-chaos-flag :value ,initial-value
			       :name ,names
			       :canon-name ,canon-name
			       :group ,group
			       :doc-string ,doc-string
			       :hook ,hook)))
     (dolist (name ,names)
       (setf (gethash name *chaos-flag-names*) ,canon-name))
     (setf (gethash ,canon-name) flg)
     flg))

;;; SAVE/RESTORE Flags
;;;
(defun save-chaos-flags ()
  (let ((flags nil))
    (maphash #'(lambda (x y)
		 (push (cons x (cflg-value y))
		       flags))
	     *chaos-control-flags*)
    flags))

(defun restore-chaos-flags (flags)
  (dolist (f flags)
    (setf (gethash (car f) *chaos-control-flags*) (cdr f)))
  t)

;;; FLAG SET utils

(defvar *chaos-flag-set* nil)

(defstruct (chaos-flag-set)
  (name "" :type simple-string)
  (flags nil :type list))

(defun find-chaos-flag-set (name)
  (declare (type simple-string name)
	   (values (or chaos-flag-set null)))
  (find-if #'(lambda (x) (string= name (chaos-flag-set-name x)))
	   *chaos-flag-set*))

(defun create-chaos-flag-set (name)
  (declare (type simple-string name))
  (let ((fset (make-chaos-flag-set :name name)))
    (setf (chaos-flag-set-flags fset) (save-chaos-flags))
    fset)
  )

(defun save-chaos-flag-set (name)
  (declare (type simple-string name))
  (let ((fset (find-chaos-flag-set name)))
    (unless (chaos-flag :quiet)
      (with-output-msg ()
	(format t "saving flags to ~a." name)))
    (if fset
	(progn
	  (unless (chaos-flag :quiet)
	    (with-output-chaos-warning ()
	      (format t "changing flag set ~a with current values." name)))
	  (setf (chaos-flag-set-flags fset) (save-chaos-flags)))
      (progn
	(setq fset (create-chaos-flag-set name))
	(push fset *chaos-flag-set*)))
    t))

(defun restore-chaos-flag-set (name)
  (declare (type simple-string name))
  (let ((fset (find-chaos-flag-set name)))
    (unless fset
      (with-output-chaos-error ('no-such-flag-set)
	(format t "no such flag set ~s." name)))
    (unless (chaos-flag :quiet)
      (with-output-msg ()
	(format t "restoring flag set from ~s." name)))
    (restore-chaos-flags (chaos-flag-set-flags fset))
    t))

;;; EOF

;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: sensible.lisp,v 1.0 2012-10-29 04:23:10 sawada Exp $
(in-package :chaos)
#|==============================================================================
				 System: Chaos
			         Module: tools
			       File: sensible.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; ****************
;;; Sensible Checker
;;; ****************

(defun check-sensible (module &optional report)
  (let ((result nil))
    (with-in-module (module)
      (let ((opinfos (module-all-operators module)))
	(dolist (opinfo opinfos)
	  (let ((r1 (check-op-sensibleness opinfo)))
	    (when r1 (push r1 result)))))
      (if result
	  (let ((*print-indent* 2))
	    (with-output-simple-msg  ()
	      (format t "<< The signature of the module is not sensible."))
	    (print-next)
	    (format t " The following overloaded operators make the signature non-sensible:")
	    (dolist (op result)
	      (dolist (p1 op)
		(let ((*print-indent* (+ 2 *print-indent*)))
		  (print-next)
		  (print-method p1 module *standard-output*)))))
	(when report
	  (with-output-simple-msg ()
	    (format t "<< The signature of the module is sensible.")))
	))))

(defun check-op-sensibleness (opinfo)
  (let ((methods (opinfo-methods opinfo))
	(vio-pair nil))
    (do* ((ms methods (cdr ms))
	  (method (car methods) (car methods)))
	((endp (cdr ms)))
      (dolist (m2 (cdr ms))
	(unless (is-sensible method m2)
	  (pushnew method vio-pair)
	  (pushnew m2 vio-pair))))
    vio-pair))

(defun is-sensible (m1 m2)
  (let* ((ar-list1 (method-arity m1))
	 (ar-list2 (method-arity m2))
	 (alen (length ar-list1))
	 (cor1 (method-coarity m1))
	 (cor2 (method-coarity m2)))
    (unless (is-in-same-connected-component cor1 cor2 *current-sort-order*)
      (return-from is-sensible nil))
    (dotimes (x alen)
      (unless (is-in-same-connected-component (nth x ar-list1)
					      (nth x ar-list2)
					      *current-sort-order*)
	(return-from is-sensible nil)))
    t))

;;; EOF

;;;-*- Mode:LISP; Package: Chaos; Base:10; Syntax:Common-lisp -*-
;;; $Id: bmacro.lisp,v 1.1.1.1 2003-06-19 08:28:34 sawada Exp $
(in-package :chaos)
#|==============================================================================
				 System: Chaos
			       Module: primitives
			       File: bmacro.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

(defstruct (macro (:print-function print-macro))
  (lhs nil :type (or null term))
  (rhs nil :type (or null term)))

(defun print-macro (macro stream &rest ignore)
  (declare (ignore ignore))
  (let ((mod (or *last-module* *current-module*)))
    (if mod
	(with-in-module (mod)
	  (term-print (macro-lhs macro) stream)
	  (terpri stream)
	  (princ " ::= ")
	  (term-print (macro-rhs macro) stream))
      (format t "#<MacroDecl: ~D>" (addr-of macro)))))

;;; EOF



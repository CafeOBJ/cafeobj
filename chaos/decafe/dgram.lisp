;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: dgram.lisp,v 1.1.1.1 2003-06-19 08:27:54 sawada Exp $
(in-package :chaos)
#|==============================================================================
			    System: CHAOS
			    Module: deCafe
			   File: dgram.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;;
;;;
;;;

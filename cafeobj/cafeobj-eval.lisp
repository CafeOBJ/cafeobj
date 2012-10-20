;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: cafeobj-eval.lisp,v 1.2 2010-06-21 07:23:00 sawada Exp $
(in-package :chaos)
#|==============================================================================
                             System: CHAOS
                            Module: cafeobj
                         File: cafeobj-eval.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;;== DESCRIPTION ==============================================================
;;; CafeOBJ top level command processors.
;;;

;;; MODULE DECLARATION
;;;
(defun cafeobj-eval-module (input)
  (declare (type list input)
           ;; (values t)
           )
  (let ((ast (process-module-declaration-form input)))
    (eval-ast ast)))

;;; VIEW DECLARATION
;;;
(defun cafeobj-eval-view (input)
  (declare (type list input)
           (values t))
  (let ((ast (process-view-declaration-form input)))
    (eval-ast ast)
    ))

;;; REDUCE/EXEC TERM
;;;
(defun cafeobj-perform-reduction (input)
  (declare (type list input)
           (values t))
  (let ((ast (process-reduce-command input)))
    (eval-ast ast)))

(defun cafeobj-perform-exec (input)
  (declare (type list input)
           (values t))
  (let ((ast (process-exec-command input)))
    (eval-ast ast)))

(defun cafeobj-perform-exec+ (input)
  (declare (type list input)
           (values t))
  (let ((ast (process-exec+-command input)))
    (eval-ast ast)))

;;; TEST REDUCTION
(defun cafeobj-test-reduction (input)
  (declare (type list input)
           (values t))
  (let ((ast (process-test-reduction input)))
    (eval-ast ast)))

;;; PARSE TERM
(defun cafeobj-parse-term (input)
  (declare (type list)
           (values t))
  (let ((ast (process-parse-command input)))
    (eval-ast ast)))

;;; EOF



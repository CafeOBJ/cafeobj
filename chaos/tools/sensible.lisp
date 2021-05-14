;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
;;;
;;; Copyright (c) 2000-2021, Toshimi Sawada. All rights reserved.
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
    (dolist (m1 methods)
      (dolist (m2 methods)
        (if (not (eq m1 m2))
            (unless (is-sensible m1 m2)
              (pushnew m1 vio-pair)
              (pushnew m2 vio-pair)))))
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

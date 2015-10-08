;;;-*- Mode:LISP; Package: Chaos; Base:10; Syntax:Common-lisp -*-
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
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

#|==============================================================================
                                 System: Chaos
                                  Module: eval
                                File: debug.lisp
==============================================================================|#

(defun print-opinfos (module)
  (with-in-module (module)
    (dolist (opinfo (module-all-operators module))
      (let ((op (opinfo-operator opinfo)))
        (print-next)
        (print-as :object opinfo)))))

(defun check-method-info (module)
  (with-in-module (module)
    (dolist (opinfo (module-all-operators module))
      (let ((methods (opinfo-methods opinfo)))
        (dolist (m methods)
          (format t "~%method : ")
          (print-chaos-object m)
          (let ((info (get-method-info m)))
            (if (not info)
              (format t "~%could not get method info ! ")
              (print-method-info info))))))))

(defun print-method-info (info)
  (let ((*print-indent* (+ 2 *print-indent*)))
    (print-next)
    (format t "** method-info ----------------------------")
    (format t "~& operator : ")
    (print-chaos-object (%method-info-operator info))
    (print-next)
    (format t " theory : ")
    (print-theory-brief (%method-info-theory info))
    (print-next)
    (format t "~& overloaded-methods : ")
    (dolist (ovm (%method-info-overloaded-methods info))
      (print-chaos-object ovm)
      (print-next))
    (format t "~& rules-with-same-top : ")
    (print-chaos-object (%method-info-rules-with-same-top info))
    (print-next)
    (format t " rules-with-different-top : ")
    (map nil #'print-chaos-object (%method-info-rules-with-different-top info))
    (print-next)
    (format t " strictly-overloaded : ")
    (print-chaos-object (%method-info-strictly-overloaded info))
    (print-next)
    (format t " rew-strategy : ")
    (print-chaos-object (%method-info-rew-strategy info))
    (print-next)
    ;;(format t " evaluator : ")
    ;;(print-chaos-object (%method-info-evaluator info))
    ))

;;; EOF

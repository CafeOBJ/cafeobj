;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
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
#|==============================================================================
                            System: CHAOS
                          Module: chaos/tools
                            File: help.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; 
;;; CafeOBJ interpreter On-Line HELP SYSTEM
;;;

(defvar *Help-DB* (make-hash-table :test #'equal))

(defun get-description (com-pat &optional (detail nil))
  (let* ((sdesc (gethash com-pat *Help-DB*))
         (syntax (first sdesc)))
    (if sdesc
        (concatenate 'string "~%[Syntax]: \"" syntax "\"~%  "
                     (if detail
                         (third sdesc)
                       (second sdesc)))
      nil)))

(defun read-help-db (path)
  (clrhash *Help-DB*)
  (with-open-file (strm path :if-does-not-exist :error)
    (loop for entry = (read strm nil :eof)
        while (not (eq entry :eof))
        do (let ((keypat (first entry))
                 (syntax (second entry))
                 (simple (third entry))
                 (detail (fourth entry)))
             (setf (gethash keypat *Help-DB*) (list syntax simple detail))))))

#|| not used
(defun setup-help-db ()
  (let ((fname (chaos-probe-file "help" *chaos-libpath* '(".desc"))))
    (unless fname
      (error "Internal error, can't find help.desc"))
    (read-help-db fname)))
||#

;;; EOF


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
                                  System:Chaos
                                 Module:e-match
                             File:match-utils.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; For Debug
;;;
(defmacro with-match-debug (&rest body)
  `(when *match-debug*
     (let ((*print-indent* (+ 2 *print-indent*))
           (*print-line-limit* 90))
       (declare (type fixnum *print-indent* *print-line-limit*))
       ,@body)))

;;; POSSIBLY-MATCHES : PATTERN TARGET -> BOOL
;;;-----------------------------------------------------------------------------
;;; returns t iff the pattern and target may match.
;;; must be accurate when answer is false.

;;; possibly-matches-non-ver
;;; assume that t1,t2 are not a variables.
;;;
(declaim (inline possibly-maches-nonvar))
(defun possibly-matches-nonvar (t1 t2)
  (declare (type term t1 t2)
           (optimize (speed 3) (safety 0))
           (values (or null t)))
  (cond ((term-is-builtin-constant? t1)
         (term-builtin-equal t1 t2))
        ((term-is-builtin-constant? t2) nil)
        (t 
         (let* ((meth1 (term-head t1))
                (meth2 (term-head t2))
                (th-info-1 (method-theory-info-for-matching meth1))
                (th-info-2 (method-theory-info-for-matching meth2)))
           (if (not (method-is-of-same-operator+ meth1 meth2))
               ;; built-in identity matching requires a change here
               ;; somehow the usage of theories seems messy here.
               (if (test-theory .Z. (theory-info-code th-info-1))
                   ;; too costly?
                   (or (possibly-matches (term-arg-1 t1) t2)
                       (possibly-matches (term-arg-2 t1) t2))
                   nil)
               (let ((chk1 (theory-info-empty-for-matching th-info-1))
                     (chk2 (theory-info-empty-for-matching th-info-2)))
                 (if (and chk1 chk2)
                     (let ((subs1 (term-subterms t1))
                           (subs2 (term-subterms t2))
                           (ok? t))
                       (while subs1
                         (unless (possibly-matches (car subs1) (car subs2))
                           (setq ok? nil)
                           (return))
                         (setq subs1 (cdr subs1)
                               subs2 (cdr subs2)))
                       ok?)
                     t)))))))

;;; could improve on this
;;; t1 : pattern
;;; t2 : term
(declaim (inline possibly-matches))
(defun possibly-matches (t1 t2)
  (declare (type term t1 t2)
           (optimize (speed 3) (safety 0))
           (values (or null t)))
  (cond ((term-is-variable? t1) t)
        ((term-is-variable? t2) nil)
        (t (possibly-matches-nonvar t1 t2))))

;;; EOF

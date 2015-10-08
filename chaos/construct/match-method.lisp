;;;-*- Mode:Lisp; Syntax:CommonLisp; Package:CHAOS -*-
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
                                Module:construct
                             File:match-method.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

(defun match-next-fail (&rest ignore)
  (declare (values t t t t))
  (declare (ignore ignore))
  (values nil nil t nil))

;;; METHODS
;;; each rewrite rule has a method in the followings:
;;;
;;(defvar *match-empty-method*     '(simp-match-e    . match-next-fail))
(defvar *match-empty-method*     '(first-match    . match-next-fail))
(defvar *match-idem-method*      '(idem-match      . match-next-fail))
(defvar *match-idem-ext-method*  '(idem-ext-match  . match-next-fail))
(defvar *match-dep-method*       '(dep-match       . match-next-fail))
(defvar *match-id-A-method*      '(id-A-match      . match-next-fail))
(defvar *match-id-AC-method*     '(id-AC-match     . match-next-fail))
(defvar *match-id-A-dep-method*  '(id-A-dep-match  . match-next-fail))
(defvar *match-id-AC-dep-method* '(id-AC-dep-match . match-next-fail))
(defvar *match-id-gen-method*    '(id-gen-match    . match-next-fail))
(defvar *match-default-method*   '(first-match     . next-match))
  
;;; CHOOSE-MATCH-METHOD : PATTERN CONDITION KIND
;;;                          -> PAIR[FIRST-MATCH-METHOD, NEXT-MATCH-MEGHOD]
;;;-----------------------------------------------------------------------------
;;; select an apropriate matching method.
;;;
(defun choose-match-method (lhs cond knd)
  (declare (type term lhs)
           (type term cond)
           (type symbol knd)
           (values list))
  (let (match-method)
    (when *on-operator-debug*
      (format t "~%[choose-match-method]: kind=~s" knd)
      (format t "~%LHS: ")
      (term-print-with-sort lhs)
      (format t "~%CND: ")
      (term-print-with-sort cond))
    (setq match-method
      (cond ((term-is-variable? lhs) *match-empty-method*)
            ((and (memq knd '(:id-theorem :id-ext-theory))
                  (theory-contains-identity (method-theory (term-head lhs))))
             ;; LHS has Identity theory.
             (let ((meth (term-head lhs)))
               (declare (type method meth))
               (if (method-is-associative meth)
                   (if (is-simple-AC-match-ok? lhs cond)
                       (if (method-is-commutative meth)
                           *match-id-AC-dep-method*
                         *match-id-A-dep-method*)
                     (if (method-is-commutative meth)
                         *match-id-AC-method*
                       *match-id-A-method*))
                 *match-id-gen-method*)))

            ;; Theory is EMPTY and simple syntactical match can be applied.
            ((simple-match-e-ok? lhs cond) *match-empty-method*)

            ;; Theory has idempotency, and simple (restricted) idem matching
            ;; can be applied.
            ((match-is-idem-ok? lhs cond knd) *match-idem-method*)

            ;; Theory has idempotency, and simple (restricted with an extension)
            ;; idem match can be applied.
            ((match-is-idem-ext-ok? lhs cond knd) *match-idem-ext-method*)

            ;; Theory has AC, and simple AC matching can be applied.
            ((is-simple-AC-match-ok? lhs cond)
             (when (null *match-dep-var*)
               (setq *match-dep-var* (make-new-variable 'REST *cosmos*)))
             *match-dep-method*)

            ;; There are no special methods available, we use general matching
            ;; method. 
            (t *match-default-method*)  ; the default
            ))
    (when *on-operator-debug*
      (format t "~%===> ~s" match-method))
    match-method))

;;; SPECIALIZED MATCHERS

;;; ASSOC with ID
;;;
(defun id-A-match (t1 t2)
  (declare (type term t1 t2))
  (first-match-with-theory the-A-property t1 t2))

;;; AC with ID
(defun id-AC-match (t1 t2)
  (declare (type term t1 t2))
  (first-match-with-theory the-AC-property t1 t2))

(defun id-A-dep-match (t1 t2)
  (declare (type term t1 t2))
  (match-dep-with-theory the-A-property t1 t2))

(defun id-AC-dep-match (t1 t2)
  (declare (type term t1 t2))
  (match-dep-with-theory the-AC-property t1 t2))

(defun id-gen-match (t1 t2)
  (declare (type term t1 t2))
  (first-match-with-theory
   (theory-code-to-info (logandc1 #..Z.
                                  (the fixnum (theory-code (method-theory
                                                            (term-head t1))))))
   t1 t2))

;;; EOF

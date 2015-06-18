;;;-*-Mode:LISP; Package: CHAOS; Base:10; Syntax:Common-lisp -*-
;;;
;;; Copyright (c) 2000-2014, Toshimi Sawada. All rights reserved.
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
;;;
(in-package :chaos)
#|=============================================================================
                             System:Chaos
                            Module:BigPink
                            File:lrpo.lisp
=============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; lrpo-lex : t1 t2 -> Bool
;;; -- returns t iff t1 > t2
;;; -- t1 and t2 must be of same operator
;;;
(defun lrpo-lex (t1 t2)
  (declare (type term t1 t2))
  (let ((subs1 (term-subterms t1))
        (subs2 (term-subterms t2)))
    (loop (unless subs1 (return))
      (unless (term-is-identical (car subs1)
                                 (car subs2))
        (return))
      (setq subs1 (cdr subs1)
            subs2 (cdr subs2)))
    (if (null subs1)
        nil                             ; identical
      (if (lrpo (car subs1) (car subs2))
          ;; is t1 > each remaining arg of t2
          (every #'(lambda (x)(lrpo t1 x))
                 (cdr subs2))
        ;; is there a remaining arg of t1 s.t. arg == t2 or arg > t2 ?
        (dolist (ra (cdr subs1) nil)
          (when (or (term-is-identical ra t2)
                    (lrpo ra t2))
            (return-from lrpo-lex t)))))))

;;; num-occurrences
;;;
(declaim (inline num-occurrences))

(defun num-occurrences (arg term)
  (declare (type term arg term)
           (values fixnum))
  (let ((i 0))
    (declare (type fixnum i))
    (dolist (sub (term-subterms term))
      (when (term-is-identical sub arg)
        (incf i)))
    i))

;;; term-multiset-diff t1 t2
(defun term-multiset-diff (t1 t2)
  (declare (type term t1 t2))
  (let ((done nil)
        (diff nil))
    (declare (type list diff))
    (dolist (sub (term-subterms t1))
      (unless (member sub done :test #'term-is-identical)
        (push sub done)
        (when (> (num-occurrences sub t1)
                 (num-occurrences sub t2))
          (push sub diff))))
    diff))

;;; lrpo-multiset
;;;
(defun lrpo-multiset (t1 t2)
  (declare (type term t1 t2))
  (let ((t1-sub (term-subterms t1))
        (t2-sub (term-subterms t2)))
    (declare (type list t1-sub t2-sub))
    (unless t1-sub (return-from lrpo-multiset nil))
    (unless t2-sub (return-from lrpo-multiset t))
    (let ((diff1 (term-multiset-diff t1 t2))
          (diff2 (term-multiset-diff t2 t1))
          (ok t))
      (declare (type list diff1 diff2))
      (if diff2
          (progn
            (dolist (r2 diff2 )
              (unless ok (return))
              (setq ok nil)
              (dolist (r1 diff1)
                (when (setq ok (lrpo r1 r2))
                  (return))))
            ok)
        nil)
      )))

;;; LRPO
;;; t iff t1 > t2
(defun lrpo (t1 t2)
  (declare (type term t1 t2))
  (let ((s1 (term-sort t1))
        (s2 (term-sort t2)))
    (declare (type sort* s1 s2))
    (when (sort< s1 s2 *current-sort-order*)
      (return-from lrpo nil))
    (when (sort< s2 s1 *current-sort-order*)
      (return-from lrpo t))
    (when (term-is-lisp-form? t1)
      (return-from lrpo nil))
    (when (term-is-lisp-form? t2)
      (return-from lrpo t))
    (when (term-is-builtin-constant? t1)
      (return-from lrpo nil))
    (when (term-is-builtin-constant? t2)
      (return-from lrpo t))
    (when (term-is-variable? t1)
      (return-from lrpo nil))
    (when (term-is-variable? t2)
      (return-from lrpo (occurs-in t2 t1)))
    ;;
    (if (method-is-of-same-operator (term-head t1) (term-head t2))
        (lrpo-lex t1 t2)
        ;; (lrpo-multiset t1 t2)
      (let ((prec (op-lex-precedence (term-head t1) (term-head t2))))
        (declare (type symbol prec))
        (if (eq prec :same)
            (lrpo-multiset t1 t2)
          (if (eq prec :greater)
              ;; t1 > each arg of t2
              (every #'(lambda (x) (lrpo t1 x))
                     (term-subterms t2))
            ;; there is an arg of t1 s.t. arg = t2 or arg > t2.
            (some #'(lambda (x)
                      (or (term-is-identical x t2)
                          (lrpo x t2)))
                  (term-subterms t1))))))
    ))

(declaim (inline lrpo-greater))

(defun lrpo-greater (t1 t2)
  (declare (type term t1 t2))
  (lrpo t1 t2))

(defun order-equalities-lrpo (clause &optional input?)
  (declare (type clause clause)
           (ignore input?))
  (dolist (lit (clause-literals clause))
    (declare (type literal lit))
    (when (eq-literal? lit)
      (let* ((eq (literal-atom lit))
             (alpha (term-arg-1 eq))
             (beta (term-arg-2 eq)))
        (declare (type term eq alpha beta))
        (if (lrpo-greater alpha beta)
            (set-bit (literal-stat-bits lit) oriented-eq-bit)
          (if (lrpo-greater beta alpha)
              (let ((new-atom
                     (make-term-with-sort-check *fopl-eq*
                                                (list beta alpha))))
                (setf (literal-atom lit) new-atom)
                (set-bit (literal-stat-bits lit) scratch-bit)
                (set-bit (literal-stat-bits lit) oriented-eq-bit)
                )))))))

;;; 
(defun pn-orient-term-pair (module pair)
  (unless (pn-flag lrpo)
    (return-from pn-orient-term-pair
      (values (car pair) (cdr pair))))
  (unless (module-proof-system module)
    (let ((*chaos-quiet* t))
      (reset-module-proof-system module)))
  (with-proof-context (module)
    (if (lrpo (car pair) (cdr pair))
        (values (car pair) (cdr pair))
      (if (lrpo (cdr pair) (car pair))
          (values (cdr pair) (car pair))
        (values (car pair) (cdr pair)))))
  )

;;; EOF

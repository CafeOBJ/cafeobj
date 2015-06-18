;;;-*- Mode:Lisp; Syntax:Common-Lisp; Package:CHAOS -*-
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
(in-package :CHAOS)
#|==============================================================================
                                 System: Chaos
                                 Module: comlib
                                File: list.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; A collection of utilities on List structure

;;; **************
;;; List Structure______________________________________________________________ 
;;; **************

;;; flatten-list
;;;  flattens list L, i.e., returns a single list containing the
;;;   same atoms as L but with any internal lists 'dissolved'.
;;; For example,
;;;   (flatten-list '(a (b c) d))  ==>  (a b c d)
;;; Recursively flattens components of L, according to the following rules:
;;;    - an atom is already flattened.
;;;    - a list whose CAR is also a list is flattened by appending the
;;;      flattened CAR to the flattened CDR (this is what dissolves internal
;;;      lists).
;;;    - a list whose CAR is an atom is flattened by just flattening the CDR
;;;      and CONSing the original CAR onto the result.
;;; These rules were chosen with some attention to minimizing CONSing."

(defun flatten-list (L)
  ;; (declare (optimize (speed 3) (safety 0)))
  (cond ((null L) '())
        ((atom L) L)
        ((consp L)
         (if (consp (car L))
             (append (flatten-list (car L)) (flatten-list (cdr L)))
             (cons (car L) (flatten-list (cdr L)))))
        ))

;;; firstn
;;;  Returns a new list the same as List with only the first N elements.

(defun firstn (list &optional (n 1))
  (declare ;; (optimize (speed 3) (safety 0))
           (type list list)
           (type fixnum n))
  (cond ((> n (length list)) list)
        ((< n 0) nil)
        (t (ldiff list (nthcdr n list)))))

;;; in-order-union
;;;   Append and remove duplicates. Like union, but the objects are
;;;   guarranteed to stay in order.

(defun in-order-union (list1 list2 &optional (test #'eql))
  (remove-duplicates (append list1 list2) :from-end t :test test))

;;; true-list-p
;;; Returns t if the term is a non-dotted list. Note that nil is a true list.

(defun true-list-p (term)
  ;; (declare (optimize (speed 3) (safety 0)))
  (and (listp term)
       (not (cdr (last term)))))

;;; rotate-list
;;; Returns a new list rotated at numth element.
;;;
(defun rotate-list (list num minusp)
  (declare (type fixnum num)
           (type t minusp))
  (let ((len (length list))
        (new-stack (copy-list list)))
    (declare (type fixnum len)
             (type list new-stack))
    (when (>= (abs num) len)
      (return-from rotate-list nil))
    (cond ((or (< num 0) (and (= num 0) minusp))
           (setq num (- len (1+ (abs num))))
           (print num)
           (setq new-stack
             (setq new-stack (nconc (nthcdr num new-stack)
                                    (firstn new-stack num))))
           )
          (t (rotatef (nth 0 new-stack)
                      (nth num new-stack))))
    new-stack))


;;; delete-nth
;;; Returns a new list deleted the nth element
;;;
(defun delete-nth (nth lst)
  (declare (fixnum nth))
  (let ((len (length lst))
        (new-lst nil))
    (when (>= nth len)
      (return-from delete-nth nil))
    (setq new-lst (nconc (firstn lst nth)
                         (nthcdr (1+ nth) lst)))
    new-lst))


;;; EOF

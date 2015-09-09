;;;-*- Mode:Lisp; Syntax:CommonLisp; Package: CHAOS -*-
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
                               File:match-c.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; PROCEDURES for C Matching ==================================================

;;; COMMUTATIVE STATE 
;;;
;;; The commutative state consists into an array of booleen and the original 
;;; system. The state of booleen represent the state of the exploration of 
;;; all the permutation. It has to be see as the representation in basis 
;;; 2 of a number < 2^r.
;;;

(defstruct (match-C-state
            ; (:type vector)
            (:constructor create-match-C-state (count sys)))
  (count 0 :type fixnum)
  (sys nil :type list))

;;; INTIALIZATION

;;; Initialize a commutative state. It check if the top symbols of each equation
;;; of the system have the same (commutative) head function.

(defun match-C-state-initialize (sys env)
  (declare (ignore env)
           (type list sys))
  (block no-match
    (dolist (equation (m-system-to-list sys))
      (unless (and (not (term-is-variable? (equation-t2 equation)))
                   (method-is-commutative-restriction-of
                    (term-method (equation-t2 equation))
                    (term-method (equation-t1 equation))))
        (return-from no-match (values nil t))))
    (values (create-match-C-state 0 sys)
            nil)))

;;; NEXT STATE

(defun match-C-next-state (C-st)
  (declare (type match-c-state))
  (let* ((N   (match-C-state-count C-st))
         (sys (match-C-state-sys C-st))
         (q   N)
         (r   0)
         (point (m-system-to-list sys))
         (equation nil)
         (t1 nil)
         (t2 nil)
         (new-sys (new-m-system))
         (lg (length point))
         )
    (declare (type fixnum q r lg N)
             (type list point))
    (if (= N (the fixnum (expt2 (the fixnum lg))))
        ;; there is no more match-C-state
        (values nil nil t)
        (progn 
          (dotimes-fixnum (k lg)
            #+KCL (setq r (rem q 2) q (truncate q 2))
            #-KCL (multiple-value-setq (q r) (truncate q 2))
            (setq equation (car point)
                  point (cdr point)
                  t1 (equation-t1 equation)
                  t2 (equation-t2 equation))
            (cond ((= r 0) 
                   (add-equation-to-m-system new-sys 
                                             (make-equation (term-arg-1 t1) 
                                                            (term-arg-1 t2)))
                   (add-equation-to-m-system new-sys 
                                             (make-equation (term-arg-2 t1) 
                                                            (term-arg-2 t2))))
                  (t (add-equation-to-m-system new-sys 
                                               (make-equation (term-arg-1 t1) 
                                                              (term-arg-2 t2)))
                     (add-equation-to-m-system new-sys 
                                               (make-equation (term-arg-2 t1) 
                                                              (term-arg-1 t2))))))
          (setf (match-C-state-count C-st) (1+ N))
          (values new-sys C-st nil)
          ))))


;;; EQUALITY

;;; "t1" and "t2" are supposed to be terms with same head commutative symbol
;;;
(defun match-C-equal (t1 t2)
  (declare (type term t1 t2))
  (if (term-is-applform? t2)
      (if (method-is-of-same-operator (term-head t1) (term-head t2))
          (if (term-equational-equal (term-arg-1 t1) (term-arg-1 t2))
              (term-equational-equal (term-arg-2 t1) (term-arg-2 t2))
              (if (term-equational-equal (term-arg-1 t1) (term-arg-2 t2))
                  (term-equational-equal (term-arg-2 t1) (term-arg-1 t2))
                  nil))
          nil)
      nil))
              

;;; EOF

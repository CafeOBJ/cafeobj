;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
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
(in-package :chaos)
#|==============================================================================
                                  System:Chaos
                                 Module:e-match
                                File:match.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

#|
                  EQUATIONAL TERM MATCHING TOP LEVEL ROUTINES
|#

;;; OBSOLETE COMMENTS:
;;; We compute a matcher in a canonicalized order-sorted signature, i.e.,
;;; associated sort of the term is computed in the signature whose sorts are
;;; disjoint, thus ground terms are associated with a single sort, and variables
;;; have a set of disjoint sorts.
;;; 
;;(defmacro match-check-sort (variable-sorts term-sort)
;;  ` (if (sort= (car ,variable-sorts) *universal-sort*)
;;        t
;;        (if (member (car ,term-sort) ,variable-sorts :test #'eq)
;;            t
;;            nil)))
;;

;;; [1]  GENERAL MATCHING 
;;;     TOP-LEVEL ROUTINES _____________________________________________________

;;; FIRST-MATCH : pattern target
;;;                  -> global-state substitution no-match-flag e-equal
;;;-----------------------------------------------------------------------------
;;; returns a first matches of 'pattern' to 'target', that is, all substitutions
;;; \sigma such that \sigma(pattern) = target. (possibly empty) other matchers
;;; will computed by NEXT-MATCH.
;;;
;;; NOTE: Assumptions of the operation:
;;;  (1) target and pattern are flattened;
;;;  (2) target contains no varibles; this guarantees that the range of \sigma is
;;;      disjoint from its domain, i.e., the \sigma is idempotent.
;;;

(defun first-match (t1 t2 &optional (sigma nil))
  (declare (type term t1 t2)
           (values list list (or null t) (or null t)))
  (when *match-debug*
    (format t "~%* First Match --------------------------------~%")
    (princ " t1 = ") (term-print-with-sort t1)
    (terpri)
    (princ " t2 = ") (term-print-with-sort t2)
    (terpri)
    (format t " unify? = ~s" *do-unify*)
    (terpri)
    (format t " one way match? = ~s" *one-way-match*)
    (force-output))
  ;;
  (multiple-value-bind (m-sys no-match) 
      ;; (match-decompose&merge (new-match-system t1 t2))
      (match-decompose&merge (create-match-system (new-environment)
                                                  (create-m-system t1 t2))
                             sigma)
    (when *match-debug*
      (format t "~%result of match-deocmpose&merge, no-match=~a" no-match)
      (force-output))
    ;; Note: if the two terms are similar then "m-sys" is empty.
    (if no-match 
        (values nil nil t nil)          ; no match
      (let ((gst (new-global-state)))
        (declare (type list gst))
        (cond ((m-system-is-empty? (match-system-sys m-sys))
               (when *match-debug*
                 (format t "~% return with success"))
               (let ((subst (match-system-to-substitution m-sys)))
                 (when *match-debug*
                   (print-substitution subst))
                 (values gst 
                         subst
                         nil
                         (null (car subst)))))
              ((match-system-e-equal m-sys)
               (values nil nil nil t))
              (t (multiple-value-bind (sys theory-info)
                     (match-system-extract-one m-sys)
                   (declare (type list sys) (type theory-info theory-info))
                   (when *match-debug*
                     (format t "~% extracted a system ")
                     (print-m-system sys))
                   ;; the matching system is not modified,
                   ;; thus we create a new match-system
                   (multiple-value-bind (th-st no-match)
                       (theory-state-match-initialize theory-info
                                                      sys
                                                      (match-system-env m-sys))
                     (declare (type t th-st) (type (or null t) no-match))
                     (if no-match
                         (values nil nil t nil)
                       (let ((next-gst nil))
                         (when *match-debug*
                           (format t "~%First match calls next-match")
                           (format t "~% old gst: ")
                           (print-global-state gst)
                           )
                         (setq next-gst
                           (global-state-push gst 
                                              (match-state-create 
                                               (match-system-modif-m-sys
                                                m-sys sys)
                                               sys
                                               theory-info
                                               th-st)))
                         (when *match-debug*
                           (format t "~% next gst :")
                           (print-global-state next-gst))
                         (multiple-value-bind (new-gst subst no-match)
                             (next-match next-gst)
                           (values new-gst subst no-match nil))))))))))))

;;; NEXT-MATCH : GLOBAL-STATE -> GLOBAL-STATE SUBSTITUTION NO-MATCH-FLAG
;;;-----------------------------------------------------------------------------
;;; next-match suppose that the system on top of gst is fully 
;;; decomposed and merged.

(defun next-match (gst)
  (declare (type list gst)
           (values list list (or null t)))
  (block the-end 
    (let (st)
      (while (global-state-is-not-empty gst)
        (when *match-debug*
          (format t "~%* Next-match : global-state = ")
          (print-global-state gst))
        (setq st (global-state-top gst))
        (multiple-value-bind (new-st no-more)
            (next-match-state st)
          (declare (type (or null match-state) new-st)
                   (type (or null t) no-more))
          (when *match-debug*
            (format t "~%** Next-match : next-match-state returns no-more = ~a" no-more)
            (unless no-more
              (format t "~%-- new state =")
              (print-match-state new-st)))
          (if no-more 
               (setq gst (global-state-pop gst))
               ;; else
               (progn
                 (setq gst (global-state-push gst new-st))
                 (let* ((m-sys (match-state-match-system new-st))
                        (sys (match-system-sys m-sys)))
                   (when (and (m-system-is-empty? sys)
                              (m-system-is-empty? (match-state-sys-to-solve new-st)))
                     ;; popping: the reasoning is that a successful state
                     ;; also terminates .
                     (setq gst (global-state-pop gst))
                     (when *match-debug*
                       (format t "~%* Next-match : return-with subst"))
                     (return-from the-end
                       (values gst
                               (match-system-to-substitution m-sys)
                               nil)))))))))
    (when *match-debug*
      (format t "~%* Next-match : return with no-match"))
    ;; no match
    (values nil nil t)))

;;; EMPTY-MATCH : PATTERN TARGET -> SUBSTITUTION NO-MATCH-FLAG
;;;-----------------------------------------------------------------------------
;;;
(defun empty-match (t1 t2)
  (declare (type term t1 t2)
           (values list (or null t)))
  (multiple-value-bind (m-sys no-match) 
      (match-decompose&merge (new-match-system t1 t2))
    (if no-match 
        (values nil t)                  ; no match
        (cond ((m-system-is-empty? (match-system-sys m-sys))
               (values (match-system-to-substitution m-sys) nil))
              (t (values nil t))))))    ; no match

;;; MATCHES? : PATTERN TARGET -> BOOL
;;;-----------------------------------------------------------------------------
;;;
(defun matches? (t1 t2)
  (declare (type term t1 t2)
           (values (or null t)))
  (multiple-value-bind  (gs subst no eeq)
      (first-match t1 t2)
    (declare (ignore gs subst))
    (or eeq (not no))))

;;; FIRST-MATCH-WITH-THEORY : THEORY PATTERN TARGET
;;;                              -> GLOBAL-STATE SUBSTITUTION NO-MATCH E-EQUAL
;;;-----------------------------------------------------------------------------
;;; returns the first matches of 'pattern' to 'target' with fixed operator theory
;;; 'theory'.
;;; 
(defun first-match-with-theory (theory-info t1 t2)
  (declare (type theory-info theory-info)
           (type term t1 t2)
           ;; (optimize (debug 3))
           )
  (multiple-value-bind (m-sys no-match) 
      (match-decompose&merge (new-match-system t1 t2))
    ;; Note that is the two terms are similar then "m-sys" is empty.
    ;; In the current code it is not signaled "E-equal", it must be corrected.
    (if no-match 
        (values nil nil t nil)          ; no match
        (let ((gst (new-global-state)))
          (declare (type list))
          (cond ((m-system-is-empty? (match-system-sys m-sys))
                 (values gst 
                         (match-system-to-substitution m-sys) 
                         nil
                         nil))
                ;; ((match-system-E-equal m-sys) 
                ;;   (values nil nil nil t)) ; match & e-equal
                (t (multiple-value-bind (sys th-ign)
                       (match-system-extract-one m-sys)
                     (declare (ignore th-ign))
                     ;; the matching system is not modified,
                     ;; thus we create a new match-system
                     (multiple-value-bind (th-st no-match)
                         (theory-state-match-initialize theory-info
                                                        sys
                                                        (match-system-env m-sys))
                       (if no-match
                           (values nil nil t nil) ; no match
                           (multiple-value-bind (new-gst subst no-match)
                               (next-match (global-state-push 
                                            gst 
                                            (match-state-create 
                                             (match-system-modif-m-sys m-sys sys)
                                             sys
                                             theory-info
                                             th-st)))
                             (values new-gst subst no-match nil nil))))))
                )))))

;;; EOF

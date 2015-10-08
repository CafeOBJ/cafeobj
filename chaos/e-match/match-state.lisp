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
                             File:match-state.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; GLOBAL STATE ===============================================================
;;;
;;; Global state for matching which contains the result of the history of
;;; the computation of all matches. Works like a stack.
;;;

(deftype global-state () 'list)

(defmacro new-global-state () nil)

(defmacro global-state-is-empty? (?___gst) `(null ,?___gst))
(defmacro global-state-is-not-empty (?_gst___?) ?_gst___?)

(defmacro global-state-pop (?_?gst) `(cdr ,?_?gst))

(defmacro global-state-top (gst?_?) `(car ,gst?_?))

(defmacro global-state-push (?gst__? ?__st?) `(cons ,?__st? ,?gst__?))

(defun print-global-state (gst)
  (declare (type global-state gst)
           (values t))
  (let ((cnt 0))
    (declare (type fixnum cnt))
    (format t "~%** global state:-------------------")
    (dolist (ms gst)
      (format t "~&[~d]" cnt)
      (print-match-state ms)
      (incf cnt))
    (format t "~&-----------------------------------")
    ))
    
;;; STATE ======================================================================
;;;

(defmacro theory-state-match-initialize
    (theory-info____? sys____? &optional env____??)
  `(funcall (theory-info-match-init-fun ,theory-info____?)
            ,sys____?
            ,env____??))

(defmacro theory-state-match-next-state
    (____theory-info? ____theory-state???)
  `(funcall (theory-info-match-next-fun ,____theory-info?) ,____theory-state???))

(defstruct (match-state
             (:constructor create-match-state
                           (is-new match-system  sys-to-solve theory-info
                                   theory-state)))
  (is-new nil :type (or null t))
  (match-system nil :type match-system)
  (sys-to-solve nil :type list)
  (theory-info nil :type theory-info)
  (theory-state nil :type t))

(defun print-match-state (ms)
  (format t "~%--Match state, match-system-env : ")
  (dolist (env (match-system-env (match-state-match-system ms)))
    (terpri)
    (princ " lhs = ")(term-print-with-sort (equation-t1 env))
    (terpri)
    (princ " rhs = ") (term-print-with-sort (equation-t2 env)))
  (format t "~&--Match state, match-system-sys : ")
  (dolist (sys (match-system-sys (match-state-match-system ms)))
    (terpri)
    (princ " lhs = ") (term-print-with-sort (equation-t1 sys))
    (terpri)
    (princ " rhs = ") (term-print-with-sort (equation-t2 sys)))
  (format t "~&--Match state, sys-to-solve :")
  (dolist (s (match-state-sys-to-solve ms))
    (terpri)
    (princ " lhs = ") (term-print-with-sort (equation-t1 s))
    (terpri)
    (princ " rhs = ") (term-print-with-sort (equation-t2 s)))
  (format t "~&-Match state, theory-info")
  (print-theory-info (match-state-theory-info ms))
  (format t "~&-Match state, theory-state")
  )

;;; returns a new match-state

(defmacro match-state-create (m-sys?_? *__sys-to-solve *__th-info *__theory-state)
  `(create-match-state t ,m-sys?_? ,*__sys-to-solve ,*__th-info ,*__theory-state))

;;; Returns a non empty decomposed and merged state.
;;; Initialize a match-state in which a match system "m-sys" has been inserted.
;;; "m-s" is supposed to be merged and ready for mutation i.e. decomposed
;;;

;;; EMPTY-STATE, see "match-e.lisp"

(defmacro match-empty-state-flag (____s) `(the fixnum (car ,____s)))
(defmacro match-empty-state-sys (____s) `(the list (cdr ,____s)))
(defmacro create-match-empty-state (flag_*_ sys_***) `(cons ,flag_*_ ,sys_***))

(defvar .match-empty-state. nil)
(eval-when (:execute :load-toplevel)
  (setq .match-empty-state. (create-match-empty-state 0 nil)))

(defun the-match-empty-state () .match-empty-state.)


;;; New match-state and true if a next match-state exists or an empty
;;; match-state and false otherwise. 
;;; --- Assume that the system to be solved is non empty.
;;; 1) looks for the next solution in the theory-state
;;; 2) it modifies the theory-state if there is a next one
;;; 3) it returns a completely new match-state
;;;
(defun next-match-state (st)
  (declare (type match-state st)
           (values (or null match-state) (or null t)))
  (let ((theory-info (match-state-theory-info st))
        (th-match-state (match-state-theory-state st)))
    ;; computes the next solution of th-match-state we quit this loop either if
    ;; there is no more new th-match-state or a new match system has been computed.
    (loop
      (multiple-value-bind (sys  new-th-match-state no-more)
          (theory-state-match-next-state theory-info th-match-state)
        (declare (type list sys)
                 (type t new-th-match-state)
                 (type (or null t) no-more))
        (if no-more 
            (return (values nil t))
          ;; "match-add-m-system" performs the decomposition and merging
          ;; and must not destroy the current match system.
          (multiple-value-bind (new-m-sys no-match)
              ;; create a new merged match-system containing the old one 
              ;; and add sys.
              (match-add-m-system (match-state-match-system st) sys)
            ;;
            (with-match-debug ()
              (let ((fun (theory-info-match-next-fun theory-info)))
                (format t "~%<--[Match-next-state] funcalled ~s" fun)))
            ;; if there is no-match, continue (the loop)
            ;; else try to returns the new match-state.
            (with-match-debug ()
              (if no-match
                  (format t "[NEXT-MATCH-STATE] retun with no-match.")))
            (unless no-match
              (multiple-value-bind (sys-to-solve theory-info) 
                  (m-system-extract-one-system (match-system-sys  new-m-sys))
                (declare (type list sys-to-solve)
                         (type theory-info theory-info))
                (if (null sys-to-solve)
                    (return (values (match-state-create new-m-sys
                                                        nil
                                                        (theory-info *the-empty-theory*)
                                                        (the-match-empty-state))
                                    nil))
                  (multiple-value-bind (th-st no-match)
                      (theory-state-match-initialize theory-info
                                                     sys-to-solve
                                                     (match-system-env new-m-sys))
                    ;; if no match, try another theory-state
                    (unless no-match 
                      ;; else modify the th-match-state of st
                      (setf (match-state-theory-state st) new-th-match-state)
                      ;; and returns
                      (return (values (match-state-create (match-system-modif-m-sys new-m-sys sys-to-solve)
                                                          sys-to-solve
                                                          theory-info
                                                          th-st)
                                      nil))))))))
          )))))
;;; EOF

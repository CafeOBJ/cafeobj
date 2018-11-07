;;;-*- Mode:LISP; Package: CHAOS; Base:10; Syntax:Common-lisp -*-
;;;
;;; Copyright (c) 2000-2018, Toshimi Sawada. All rights reserved.
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
#|=============================================================================
                                    System:CHAOS
                                   Module:cafein
                                 File:reducer.lisp
=============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 1) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))


;;; ========
;;; REDUCER
;;; provides term rewriting eclosed within computing environment.
;;; ========
(let ((*m-pattern-subst* nil)
      (.rwl-context-stack. nil)
      (.rwl-states-so-far. 0)
      (*rewrite-exec-mode* nil)
      (*rewrite-semantic-reduce* nil)
      ($$mod nil)
      (*steps-to-be-done* 0)
      ($$matches 0)
      (*perform-on-demand-reduction* nil)
      (*rule-count* 0)
      (*term-memo-hash-hit* 0)
      ($$term nil)
      ($$term-context nil)
      ($$cond nil)
      ($$target-term nil)
      ($$norm nil)
      (*do-empty-match* nil)
      (parse-begin-time 0)
      (time-for-parsing 0.0)
      (rewrite-begin-time 0)
      (time-for-rewriting 0.0))
  (declare (special *m-pattern-subst*
                    .rwl-context-stack.
                    .rwl-states-so-far.
                    *rewrite-exec-mode*
                    *rewrite-semantic-reduce*
                    $$mod
                    *steps-to-be-done*
                    $$matches
                    *perforom-on-demand-reduction*
                    *rule-count*
                    *term-memo-hash-hit*
                    $$target-term
                    $$term
                    $$term-context
                    $$cond
                    $$target-term
                    $$norm
                    *do-empty-match*))
  (declare (type (or null t) *perform-on-demand-reduction* *do-empty-match*)
           (type fixnum *steps-to-be-done* $$matches *rule-count* .rwl-states-so-far.
                 *term-memo-hash-hit*)
           (type list *m-pattern-subst* .rwl-context-stack.)
           (type (or null module) $$mod)
           (type integer parse-begin-time rewrite-begin-time)
           (type float time-for-parsing time-for-rewriting))

  (defun reset-parse-time ()
    (setf time-for-parsing 0.0))

  (defun begin-parse ()
    (setf parse-begin-time (get-internal-run-time)))

  (defun end-parse ()
    (setf time-for-parsing (elapsed-time-in-seconds parse-begin-time
                                                    (get-internal-run-time))))

  (defun time-for-parsing-in-seconds ()
    time-for-parsing)
  
  (defun begin-rewrite ()
    (setf rewrite-begin-time (get-internal-run-time)))
  
  (defun end-rewrite ()
    (setf time-for-rewriting (elapsed-time-in-seconds rewrite-begin-time
                                                      (get-internal-run-time))))

  (defun time-for-rewriting-in-seconds ()
    time-for-rewriting)

  (defun number-matches ()
    $$matches)
  
  (defun number-rewritings ()
    *rule-count*)

  (defun number-memo-hits ()
    *term-memo-hash-hit*)

  (defun number-hash-size ()
    (declare (inline hash-table-count))
    ;; .hash-size.
    (hash-table-count *term-memo-table*))

  (defun clear-rewriting-fc (module mode)
    (setf *m-pattern-subst* nil
          .rwl-context-stack. nil
          .rwl-sch-context. nil
          .rwl-states-so-far. 0
          *steps-to-be-done* 1
          *do-empty-match* nil
          *rewrite-exec-mode* (or (eq mode :exec) (eq mode :exec+))
          *rewrite-semantic-reduce* (and (eq mode :red)
                                         (module-has-behavioural-axioms module))))

  ;; prepare-term
  ;; NOTE: this always record the time cosumed for parsing the given term.
  (defun prepare-term (pre-term module)
    (declare (type module module))
    ;; be ready for parsing
    (prepare-for-parsing module)
    ;; setup target term
    (if (term? pre-term)
        (setq $$target-term pre-term)
      ;; not yet parsed term
      (progn
        (reset-parse-time)
        (begin-parse)
        (let* ((*parse-variables* nil)
               (target-term (simple-parse module pre-term *cosmos*)))
          (end-parse)
          (when (or (null (term-sort target-term))
                    (sort<= (term-sort target-term) *syntax-err-sort* *chaos-sort-order*))
            (with-output-chaos-error ('invalid-target-term)
              (format t "Could not parse the reduction target ~s" pre-term)))
          (setq $$target-term target-term))))
    ;; setup $$term
    (reset-target-term $$target-term module module)
    $$target-term)

  ;; reset-rewrite-counters
  ;; initialize rewriting counters.
  (defun reset-rewrite-counters ()
    (setf $$matches 0
          *rule-count* 0
          *term-memo-hash-hit* 0))

  ;; reset-term-memo-table
  (defun reset-term-memo-table (module)
    (when (or *clean-memo-in-normalize*
              (not (eq module *memoized-module*)))
      (clear-term-memo-table *term-memo-table*)
      (setq *memoized-module* module)))

  ;; prepare-reduction-env
  ;; all-in-one proc for setting up environment variables for rewriting,
  ;; returns evaluated 'context-module'.
  (defun prepare-reduction-env (term context-module mode stat-reset)
    (let ((module (if (module-p context-module)
                      context-module
                    ;; we got a module expression
                    (eval-modexp context-module))))
      (unless (module-p module)
        (with-output-chaos-error ('invalid-context)
          (format t "Invalid context module ~s" context-module)))
      ;; initialize term memo iff proposed rewring context is different from the current one.
      (reset-term-memo-table module)
      ;; setup target term
      (prepare-term term module)
      ;; reset statistics
      (when stat-reset (reset-rewrite-counters))
      ;; set up various flags and counters used in rewriting process
      (clear-rewriting-fc module mode)
      ;; returns the evaluated context module
      module))
    
  ;; generate-statistics-form
  (defun generate-statistics-form ()
    (let ((stat-form ""))
      (declare (type string stat-form))
      (setq stat-form
        (format nil "(~a sec for parse, ~a sec for ~d rewrites + ~d matches"
                (format nil "~,4f" (time-for-parsing-in-seconds))
                (format nil "~,4f" (time-for-rewriting-in-seconds))
                (number-rewritings)
                (number-matches)))
      (concatenate 'string stat-form
                   (if (zerop (number-memo-hits))
                       ")"
                     (format nil ", ~d memo hits)" 
                             (number-memo-hits)
                             ;; (number-hash-size)
                             )))))
  
  (defun generate-statistics-form-rewriting-only ()
    (let ((stat-form ""))
      (declare (type string stat-form))
      (setf stat-form
        (format nil "(consumed ~a sec, including ~d rewrites + ~d matches"
                (format nil "~,4f" (time-for-rewriting-in-seconds))
                (number-rewritings)
                (number-matches)))
      (concatenate 'string stat-form
                   (if (zerop (number-memo-hits))
                       ")"
                     (format nil ", ~d memo hits)" 
                             (number-memo-hits)
                             ;; (number-hash-size)
                             )))))

  ;; REDUCER
  ;; perform reduction
  (defun reducer (term context-module rewrite-mode &optional (no-stat nil))
    (with-in-module ((prepare-reduction-env term context-module rewrite-mode 
                                            (if no-stat 
                                                nil
                                              t)))
      ;; be ready for rewriting
      (!setup-reduction *current-module*)
      ;; now start 
      (unless no-stat
        (begin-rewrite))
      ;; do the reduction
      (catch 'rewrite-abort
        (if *rewrite-exec-mode*
            (rewrite-exec $$target-term *current-module* rewrite-mode)
          (rewrite $$target-term *current-module* rewrite-mode)))
      (unless no-stat
        (end-rewrite))
      $$term))

  ;; REDUCER-NO-STAT
  ;; perform reduction, but does not maintain statistical data
  ;; caller is responsible for calling
  ;;    (reset-rewrite-counters)-(begin-rewrite)-(end-rewrite)
  (defun reducer-no-stat (term context-module rewrite-mode)
    (reducer term context-module rewrite-mode :no-stat))
      
  (defun simplify-on-top (term context-module)
    (declare (type term term)
             (values t))
    (with-in-module ((prepare-reduction-env term context-module :red nil))
      (catch 'rewrite-abort
        (if (term-is-application-form? term)
            (apply-rules-with-different-top term
                                            (method-rules-with-different-top
                                             (term-head term)))
          term))))
  )


;;; EOF
      


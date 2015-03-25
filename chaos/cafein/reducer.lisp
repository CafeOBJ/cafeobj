;;;-*- Mode:LISP; Package: CHAOS; Base:10; Syntax:Common-lisp -*-
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

(let (*m-pattern-subst*
      .rwl-context-stack.
      .rwl-states-so-far.
      *rewrite-exec-mode*
      *rewrite-semantic-reduce*
      $$mod
      *steps-to-be-done*
      $$matches
      *perform-on-demand-reduction*
      *rule-count*
      *term-memo-hash-hit*
      $$term
      $$target-term
      $$norm
      *do-empty-match*
      parse-begin-time
      time-for-parsing
      rewrite-begin-time
      time-for-rewriting)
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
		    $$norm
		    *do-empty-match*))
  (declare (type (or null t) *perform-on-demand-reduction* *do-empty-match*)
	   (type fixnum *steps-to-be-done* $$matches *rule-count* .rwl-states-so-far.
		 *term-memo-hash-hit*)
	   (type list *m-pattern-subst* .rwl-context-stack.)
	   (type module $$mod)
	   (type integer parse-begin-time rewrite-begin-time)
	   (type float time-for-parsing time-for-rewriting)
	   (type term $$term $$target-term $$norm))

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

  ;; prepare-term
  (defun prepare-term (pre-term module)
    (declare (type module module))
    ;; be ready for parsing
    (prepare-for-parsing module)
    ;; setup target term
    (if (termp pre-term)
	(setq $$target-term pre-term)
      ;; not yet parsed term
      (progn
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
  (defun reset-rewrite-counters ()
    (setf $$matches 0
	  *rule-count* 0
	  *term-memo-hash-hit* 0))

  ;; prepare-reduction-env
  ;; setup environment variables.
  (defun prepare-reduction-env (term context-module mode stat-reset)
    (let ((module (if (module-p context-module)
		      context-module
		    (eval-modexp context-module))))
      (unless (module-p module)
	(with-output-chaos-error ('invalid-context)
	  (format t "Invalid context module ~s" context-module)))

      ;; initialize term memo iff proposed rewrring context is different with the current.
      (unless (eq module (get-context-module))
	(clear-term-memo-table *term-memo-table*))
      ;; setup target term
      (prepare-term term module)
      ;; reset statistics
      (when stat-reset (reset-rewrite-counters))
      ;; set up various flags and counters
      (setf *m-pattern-subst* nil
	    .rwl-context-stack. nil
	    .rwl-sch-context. nil
	    .rwl-states-so-far. 0
	    *steps-to-be-done* 1
	    *do-empty-match* nil
	    *rewrite-exec-mode* (or (eq mode :exec) (eq mode :exec+))
	    *rewrite-semantic-reduce* (and (eq mode :red)
					   (module-has-behavioural-axioms module)))
      module))
    
  ;; generate-statistics-form
  (defun generate-statistics-form ()
    (let (stat-form)
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
		     (format nil ", ~d memo hits)" (number-memo-hits))))))
  
  (defun generate-statistics-form-rewriting-only ()
    (let (stat-form)
      (declare (type string stat-form))
      (setf stat-form
    	(format nil "(consumed ~a sec, including ~d rewrites + ~d matches"
		(format nil "~,4f" (time-for-rewriting-in-seconds))
		(number-rewritings)
		(number-matches)))
      (concatenate 'string stat-form
		   (if (zerop (number-memo-hits))
		       ")"
		     (format nil ", ~d memo hits)" (number-memo-hits))))))

  ;; REDUCER
  ;; perform reduction
  (defun reducer (term context-module rewrite-mode)
    (with-in-module ((prepare-reduction-env term context-module rewrite-mode t))
      ;; be ready for rewriting
      (!setup-reduction *current-module*)
      ;; now start 
      (begin-rewrite)
      ;; do the reduction
      (catch 'rewrite-abort
	(if *rewrite-exec-mode*
	    (rewrite-exec $$target-term *current-module* rewrite-mode)
	  (rewrite $$target-term *current-module* rewrite-mode)))
      (end-rewrite)
      $$term))

  ;; REDUCER-NO-STAT
  ;; perform reduction, but does not maintain statistical data
  ;; caller is responsible for calling
  ;;    (reset-rewrite-counters)-(begin-rewrite)-(end-rewrite)
  (defun reducer-no-stat (term context-module rewrite-mode)
    (with-in-module ((prepare-reduction-env term context-module rewrite-mode nil))
      (catch 'rewrite-abort
	(if *rewrite-exec-mode*
	    (rewrite-exec $$target-term *current-module* rewrite-mode)
	  (rewrite $$target-term *current-module* rewrite-mode))))
    $$term)
      
  )


;;; EOF
      


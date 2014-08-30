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
			  File:proof-sys.lisp
=============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;;*****************************************************************************
;;;		 PROOF SYSTEM ASSOCIATED WITH MODULE
;;;*****************************************************************************

;;; extend module info

(defmacro module-proof-system (_mod)
  `(getf (object-misc-info ,_mod) :proof-system))
	
(defun create-module-psystem (mod)
  (declare (type module mod))
  (if (module-proof-system mod)
      (let ((psys (module-proof-system mod)))
	(initialize-psystem psys mod))
    (setf (module-proof-system mod)
      (make-psystem :module mod
		    :clause-hash (make-hash-table :test #'eql)
		    :demodulators (make-hash-table :test #'eq)))
    ))

(defun update-module-proof-system (mod &optional do-anyway)
  (declare (type module mod)
	   (ignore do-anyway))
  (let ((clear-passive nil))
    (when (need-rewriting-preparation mod)
      (compile-module mod)
      (setq clear-passive t)
      (setq do-anyway t))
    (unless (module-proof-system mod)
      (setq do-anyway t))

    (let ((psystem (create-module-psystem mod)))
      (when clear-passive
	(setf (psystem-passive psystem) nil))
      ;; reset clause counter
      (reset-clause-db psystem)
      ;; generate axioms in clause form
      (module-axioms->clause psystem)
      ;; may introduce skolem functions.
      (prepare-for-parsing mod)
      ;;
      psystem)))

(defun reset-module-proof-system (module)
  (declare (type module module))
  ;; setup lexical precedence of symbols.
  (make-op-lex-prec-table module)
  ;; reset db:
  (update-module-proof-system module t))

;;; PN-DB-RESET
;;;
(defun pn-db-reset (&optional (mod (or *current-module*
				       *last-module*)))
  (clear-all-index-tables)
  (reset-module-proof-system mod))

(defun auto-db-reset (module)
  (compile-module module)
  (unless (module-proof-system module)
    (create-module-psystem module))
  (unless (psystem-axioms (module-proof-system module))
    (pn-db-reset module)))

;;; CONTEXT MAKING MACRO

(defmacro with-proof-context ((_module_) &body body)
  (once-only (_module_)
    `(block with-proof-context
       (block with-in-module
	 (let* ((*current-module* ,_module_)
		(*current-sort-order* (module-sort-order *current-module*))
		(*current-opinfo-table* (module-opinfo-table *current-module*))
		(*current-ext-rule-table* (module-ext-rule-table *current-module*)))
	    (declare (special *current-module*
			      *current-sort-order*
			      *current-opinfo-table*
			      *current-ext-rule-table*))
	    (let* ((*current-proof-system* *current-module*)
		   (*current-psys* (module-proof-system *current-module*))
		   (*clause-hash* (psystem-clause-hash *current-psys*))
		   (*sos* (psystem-sos *current-psys*))
		   (*usable* (psystem-usable *current-psys*))
		   (*demodulators* (psystem-demodulators *current-psys*))
		   (*passive* (psystem-passive *current-psys*))
		   (*clause-given* nil)
		   )
	      (declare (special *current-proof-system*
				*current-psys*
				*clause-hash*
				*sos*
				*usable*
				*clause-given*
				*passive*))
	    ;;
	    ,@body)
	    )))))

;;; EOF


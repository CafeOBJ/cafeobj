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
				 System: CHAOS
				 Module: tools
			      File: describe.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;;=============================================================================
;;; HANDLERS for `show' & `describe' commands
;;;=============================================================================

;;; DESCRIBE MODULE
;;;
(defun filter-hard-sorts (sort-list)
  (remove-if #'(lambda (x) (module-is-hard-wired (sort-module x)))
	     sort-list))

(defun filter-hard-opinfos (opinfo-list)
  (remove-if #'(lambda (x) (module-is-hard-wired
			    (operator-module (car x))))
	     opinfo-list))

(defparameter .separator-bold.
  "======================================================================")
(defparameter .separator-thin.
  "----------------------------------------------------------------------")
(defparameter .under-line.
  "______________________________________________________________________")

(defun describe-module (mod &optional (print-indent *print-indent*))
  (when (module-is-inconsistent mod)
    (format t "module is inconsistent and cannt be described")
    (print-next)
    (format t "please redefine it from the scratch.")
    (flush-all)
    (return-from describe-module nil))
  (compile-module mod)
  (with-in-module (mod)
    (let ((*print-indent* print-indent))
      (fresh-line)
      (print-indent #\space)
      ;; ---------- TITLE: name, kind, type, protected mode
      (princ .separator-bold.)
      (print-next)
      (let ((title 
	     (with-output-to-string (str)
	       (let ((*standard-output* str))
		 (princ "module ")
		 (print-mod-name mod))
	       str)))
	(print-centering title))
      (print-next)
      ;; ---------- kind
      (case (module-kind mod)
	(:theory (print-centering "kind: theory"))
	(:object (print-centering "kind: object"))
	(otherwise (print-centering "kind: loose")))
      (print-next)
      ;;---------- type
      (case (module-type mod)
	(:user (print-centering "type: user defined"))
	(:system (print-centering "type: built-in module"))
	(:hard (print-centering "type: hard wired built-in"))
	(otherwise (print-centering "type: user defined")))
      (print-next)
      ;; ---------- creation date
      (if (module-creation-date mod)
	  (print-centering (concatenate 'string "created: "
					(get-time-string (module-creation-date mod))))
	  (print-centering "date defined: unknown"))
      (print-next)
      ;; ---------- protected?
      (when (module-is-write-protected mod)
	(print-centering "* module is protected (disable redefinition) *")
	(print-next))
      ;;
      (princ .separator-thin.)
      (terpri)

      ;; ---------- parameter
      ;; (when (module-parameters mod)
      ;;   (terpri)
      ;;   (print-centering "<< parameters >>")
      ;;   (let ((*print-indent* (+ 2 *print-indent*)))
      ;;   (print-module-parameters mod))
      ;;   (print-next))
      (when (get-module-parameters mod)
	(terpri)
	(print-centering "<< parameters >>")
	(let ((*print-indent* (+ 2 *print-indent*)))
	  (print-module-parameters mod))
	(print-next))

      ;; ---------- direct submodules
      (let ((subs (get-non-parameter-submodules mod)))
	(when subs
	  (terpri)
	  (print-centering "<< submodules >>")
	  (let ((*print-indent* (+ 2 *print-indent*)))
	    (print-submodule-list subs))
	  (print-next)))
      ;; ---------- sorts
      (let ((sorts (if (module-is-hard-wired mod)
		       (module-all-sorts mod)
		       (filter-hard-sorts (module-all-sorts mod)))))
	(when sorts
	  (terpri)
	  (print-centering "<< sorts and subsort relations >>")
	  (let ((*print-indent* (+ 2 *print-indent*)))
	    (print-module-sorts mod nil t)
	    )
	  (print-next)))
      ;; ---------- variables
      (let ((vars (mapcar #'cdr (module-variables mod)))
	    (rvars nil)
	    (pvars nil))
	(dolist (v vars)
	  (if (term-is-variable? v)
	      (push v rvars)
	    (push v pvars)))
	(when rvars
	  (terpri)
	  (print-centering "<< variables >>")
	  (let ((*print-indent* (+ 4 *print-indent*))
		(*print-with-sort* t))
	    (print-next)
	    (print-obj-list rvars)))
	(when pvars
	  (terpri)
	  (print-centering "<< psued variables >>")
	  (let ((*print-indent* (+ 4 *print-indent*))
		(*print-with-sort* t))
	    (print-next)
	    (print-obj-list pvars)))
	(when (or rvars pvars)
	  (print-next)))
      ;; ---------- operators & axioms
      (when (module-all-operators mod)
	(terpri)
	(print-centering "<< operators and axioms >>")
	(terpri)
	(terpri)
	(print-module-ops mod nil t))
      ;;
      (fresh-line)
      (values)
      ))
  (flush-all))

;;; DESCRIBE-OPERATOR-BRIEF
;;; * must be executed in the context of `with-in-module'.
;;;
(defun describe-operator-brief (opinfo)
  (let* ((op (opinfo-operator opinfo))
	 (methods (opinfo-methods opinfo))
	 (header (with-output-to-string (n)
		   (let ((*standard-output* n))
		     (princ (operator-symbol op))
		     ;; (princ (operator-print-name op))
		     (when (and *on-debug*
				(not (eq (operator-module op) *current-module*)))
		       (princ ".")
		       (print-mod-name (operator-module op)
				       *standard-output* t t))
		     ;; attribute
		     (let ((strat (let ((val (operator-strategy op)))
				    (if (print-check-bu op val) nil val)))
			   (thy (operator-theory op)))
		       (when (or strat (not (eq (theory-info thy) the-e-property)))
			 (let ((flag nil))
			   (princ " default attributes") (princ " { ")
			   (when (not (eq (theory-info thy) the-e-property))
			     (setq flag t)
			     (print-theory-brief thy))
			   (print-check)
			   (when strat
			     (if flag (princ " ") (setq flag t))
			     (princ "strat: ") (print-simple strat))
			   (print-check)
			   (princ " }")))))
		   n))
	 ;; (n-len (length header))
	 )
    (print-next)
    (print-centering header ".")
    #||
    (format t "~a" header)
    (if (< n-len (- *print-line-limit* *print-indent*))
	(dotimes (x (- *print-line-limit* n-len *print-indent*))
	  (princ "_"))
	(princ "*"))
    ||#
    ;; declarations with axioms
    (let ((*print-indent* (+ 2 *print-indent*)))
      (dolist (meth (reverse methods))
	(when (or (not (method-is-error-method meth))
		  (method-is-user-defined-error-method meth))
	  (print-next)
	  (princ "* rank: ")
	  (let ((arity (method-arity meth))
		(coarity (method-coarity meth)))
	    (when arity
	      (print-sort-list arity *current-module*)
	      (princ " "))
	    (princ "-> ")
	    (print-sort-name coarity *current-module*)
	    (when (and *on-debug* (not (eq *current-module* (method-module meth))))
	      (princ " (<== ")
	      (print-mod-name (method-module meth) *standard-output* t t)
	      (princ ")")))
	  (print-method-attrs meth "- attributes: ")
	(let ((axioms (method-all-rules meth)))
	  (let ((*print-indent* (+ 2 *print-indent*)))
	    (when axioms
	      (print-next)
	      (princ "- axioms:")
	      (let ((*print-indent* (+ 2 *print-indent*)))
		(dolist (rl axioms)
		  (print-next)
		  (print-axiom-brief rl)))))))))
    (flush-all)
    ))

;;; DESCRIBE-SORT sort
;;; * must be run in `with-in-module'
;;;
(defun describe-sort (sort &optional (module *current-module*))
  (if (sort-is-hidden sort)
      (princ "Hidden sort ")
      (princ "Sort "))
  (print-sort-name sort module)
  (princ " declared in the module ")
  (print-mod-name (sort-module sort))
  (let ((subs (subsorts sort))
	(supers (supersorts-no-err sort))
	(*print-indent* (+ 2 *print-indent*)))
    (when (or subs supers)
      (print-next)
      (princ "- subsort relations :")
      (print-next)
      (print-sort-graph sort))
    (when (sort-is-builtin sort)
      (print-next)
      (princ "- builtin infos : ")
      (princ (bsort-info sort)))
    (when (sort-derived-from sort)
      (print-next)
      (princ "- derived from : ")
      (print-sort-name (sort-derived-from sort) module))
    #||
    (when (the-err-sort sort (module-sort-order module))
      (print-next)
      (princ "- error sort : ")
      (print-sort-name (the-err-sort sort (module-sort-order module))))
    ||#
    (flush-all)
    ))

;;; DESCRIBE-OPERATOR
;;;
(defun describe-operator (opinfo &optional (module *current-module*))
  (with-in-module (module)
    (let* ((op (opinfo-operator opinfo))
	   (syntax (operator-syntax op))
	   (prec (opsyntax-prec syntax))
	   (cprec (opsyntax-cprec syntax))
	   (theory (operator-theory op))
	   (assoc (opsyntax-assoc syntax))
	   (strat (operator-strategy op))
	   (methods (opinfo-methods opinfo)))
      (fresh-line)
      (dotimes (x .terminal-width.) (princ "="))
      ;; (format t "~%name                : ~a" (operator-symbol op))
      (format t "~%name                : ~a" (operator-print-name op))
      (format t "~%module              : ") (print-chaos-object (operator-module op))
      (format t "~%number of arguments : ~d" (operator-num-args op))
      (format t "~%default attributes  :")
      (format t "~% rewrite strategy   : ~a" (if strat strat
						 "not specified"))
      (format t "~% syntax             :")
      (when *on-debug*
	(format t "~%   type             : ~s" (opsyntax-type syntax))
	(format t "~%   mixfix           : ~s" (operator-is-mixfix op)))
      (format t "~%   precedence       : ~a" (if prec prec "not specified"))
      (unless (eql prec cprec)
	(format t "~%   computed prec.   : ~s" cprec))
      (if assoc
	  (format t "~%   assoc            : ~s" (if (eq assoc :right)
						   'right
						   'left)))
      (format t "~%   form             : ")
      (let ((m (car methods)))
	(dolist (x (method-form m))
	  (cond ((and (consp x) (eq (car x) 'argument))
		 (princ "(")
		 (princ "arg:")
		 (princ (second x))
		 ;; (print-sort-name (cddr x))
		 (princ ")"))
		((and (consp x) (eq (car x) 'token))
		 (prin1 (string (cdr x))))
		(t (princ x)))
	  (princ " ")))
      (format t "~& theory             : ") (print-theory-brief theory)
      (when *on-debug*
	(format t "~%internal name       : ~s" (operator-print-name op)))
      
      (let ((*print-indent* (+ *print-indent* 2)))
	(dolist (m methods)
	  (terpri)
	  (dotimes (x .terminal-width.)(princ "-"))
	  (format t "~&rank                : ")
	  (when (method-arity m)
	    (print-sort-list (method-arity m) *current-module*)
	    (princ " "))
	  (princ "-> ")
	  (print-sort-name (method-coarity m) *current-module*)
	  (when (or (method-constructor m)
		    (method-has-memo m))
	    (princ "  { ")
	    (when (method-constructor m)
	      (princ "constr "))
	    (when (method-has-memo m)
	      (princ "memo "))
	    (when (method-is-meta-demod m)
	      (princ "demod "))
	    (princ "}"))
	  (print-next)
	  (format t "module            : ")
	  (print-mod-name (method-module m))
	  (print-next)
	  (format t "theory            : ")
	  (print-theory-brief (method-theory m))
	  (print-next)
	  (format t "rewrite strategy  : ~s" (method-rewrite-strategy m))
	  (when (not (eql prec (get-method-precedence m)))
	    (print-next)
	    (format t "precedence        : ~d" (get-method-precedence m))
	    )
	  (when (not (equal assoc (method-associativity m)))
	    (print-next)
	    (format t "associativity     : ~a"
		    (case (method-associativity m)
		      (:right "right")
		      (:left "left")
		      (otherwise "not specified")))
	    )
	  ;; lower methods
	  (when (method-lower-methods m)
	      (print-next)
	      ;; (format t "lower declarations:")
	      (format t "lower operations   :")
	      (let ((*print-indent* (+ 2 *print-indent*)))
		(dolist (x (reverse (method-lower-methods m)))
		  (print-next)
		  (when (method-arity x)
		    (print-sort-list (method-arity x) *current-module*)
		    (princ " "))
		  (princ "-> ")
		  (print-sort-name (method-coarity x) *current-module*))))
	  (when *on-debug*
	    ;; overloaded methods
	    (let ((ov (nreverse (remove m (method-overloaded-methods m)))))
	      (when ov
		(print-next)
		(format t "overloaded ops.   :")
		(let ((*print-indent* (+ 2 *print-indent*)))
		  (dolist (x ov)
		    (print-next)
		    (when (method-arity x)
		      (print-sort-list (method-arity x) *current-module*)
		      (princ " "))
		    (princ "-> ")
		    (print-sort-name (method-coarity x) *current-module*))))))
	  ;;
	  (when (method-derived-from m)
	    (let ((o-m (method-derived-from m)))
	      (print-next)
	      (format t "derived from      : ~s of " (method-symbol o-m))
	      (print-mod-name (method-module o-m) *standard-output* t t)))
	  ;; axioms
	  (print-next)
	  (format t "axioms            :")
	  (let ((*print-indent* *print-indent*)
		(r-ring (method-rules-with-same-top m)))
	    (unless (rule-ring-is-empty r-ring)
	      (do ((ax (initialize-rule-ring r-ring) (rule-ring-next r-ring)))
		  ((eq (rule-ring-current r-ring) (rule-ring-mark r-ring)))
		(print-next)
		(print-rule ax)
		))
	    (dolist (ax (method-rules-with-different-top m))
	      (print-next)
	      (print-rule ax)
	      ))
	  ))))
  (flush-all))

(defun print-merged (mod)
  (and *open-module*
       (equal "%" (module-name mod))))

;;; SHOW-MODULE
;;;-----------------------------------------------------------------------------

(defun show-module (mod &optional (syntax *show-mode*))
  (when (module-is-inconsistent mod)
    (with-output-chaos-warning ()
      (format t "module is inconsisted and cannot be shown, please redefine it!")
      (return-from show-module nil)))
  (compile-module mod)
  (case syntax
    (:cafeobj (show-module-in-cafeobj-syntax mod))
    (:chaos (show-module-in-chaos-syntax mod))
    (otherwise (with-output-panic-message ()
		 (format t "illegal show mode ~s" syntax))
	       (return-from show-module nil))))

(defun show-module-in-cafeobj-syntax (mod)
  (with-in-module (mod)
    (let* ((merged (print-merged mod))
	   (mod-name (with-output-to-string (m)
		       (if merged
			   (print-mod-name *open-module* m nil t)
			 (print-mod-name mod m nil t))
		       m))
	   (kind (module-kind mod))
	   (type (module-type mod))
	   (omit (if (or (memq type '(:system :hard))
			 (and merged (module-p *open-module*)
			      (memq (module-type *open-module*)
				    '(:system :hard))))
		     *kernel-hard-wired-builtin-modules*
		   *print-ignore-mods*))
	   (*print-line-limit* 80))
      ;;
      (fresh-line)
      (print-indent #\space)
      (case kind
	(:object (case type
		   (:hard (princ "hwd:mod! "))
		   (:system (princ "sys:mod! "))
		   (otherwise (princ "module! "))))
	(:theory (case type
		   (:hard (princ "hwd:mod* "))
		   (:system (princ "sys:mod* "))
		   (otherwise (princ "module* "))))
	(:ots (case type
		(:hard (princ "hwd:ots "))
		(:system (princ "sys:ots "))
		(otherwise (princ "ots "))))
	(otherwise (case type
		     (:hard (princ "hwd:mod "))
		     (:system (princ "sys:mod "))
		     (otherwise (princ "module ")))))
      (princ mod-name)
      ;; PARAMETERS
      (let ((params (get-module-parameters mod)))
	(when params
	  (let ((*print-indent* (+ (length mod-name) 9 *print-indent*)))
	    ;; (princ " [")
	    (princ " (")
	    (let ((flg nil))
	      (dolist (sb params)
		(if flg (princ ", ") (setf flg t))
		(print-check)
		(let ((mode (string-downcase
			     (string (parameter-imported-mode sb))))
		      (arg-name (parameter-arg-name sb))
		      (cntxt (parameter-context sb)))
		  (unless (equal "protecting" mode)
		    (format t "~a " mode))
		  (if (or (null cntxt) (eq mod cntxt))
		      (format t "~a :: " arg-name)
		    (progn
		      (format t "~a." arg-name)
		      (print-mod-name cntxt *standard-output* t t)
		      (princ " :: ")))
		  ;; (print-mod-name (cdar sb))
		  (print-parameter-theory-name (parameter-theory-module sb)
					       *standard-output*
					       :simple
					       :no-param)
		  )))
	    ;; (princ "]")
	    (princ ")"))))
      ;; principal sort
      (when (module-principal-sort mod)
	(fresh-line)
	(format t "      principal-sort ")
	(print-sort-name (module-principal-sort mod) mod))
      (fresh-line)
      ;; module body
      (princ "{")
      (when merged (princ " ** opening"))
      (let ((*print-indent* (+ *print-indent* 2)))
	;; IMPORTING MODULES
	(let ((subs nil)
	      (skip (if merged
			(nconc (list *open-module*) omit)
			omit)))
	  (dolist (sub (module-submodules mod))
	    (when (and (not (module-is-parameter-theory (car sub)))
		       (if *chaos-verbose*
			   t
			 (not (member (car sub) skip :key #'(lambda(x)
							      (module-name x)))))
		       (not (eq (cdr sub) :using)))
	      (push sub subs)))
	  (when subs
	    (print-next)
	    (princ "imports {")
	    (let ((*print-indent* (+ *print-indent* 2)))
	      (let ((flg nil))
		(print-next)
		(dolist (sb subs)
		  (when (not (member (car sb) skip))
		    (if flg (print-next) (setf flg t))
		    (print-check)
		    ;; importation-mode
		    (format t "~a " (string-downcase (string (cdr sb))))
		    ;; alias
		    (let ((a-name (cdr (assoc (car sb) (module-alias mod)))))
		      (when a-name
			(format t "as ~a " a-name)))
		    ;; modexpr
		    (let ((*print-indent* (+ 4 *print-indent* (length (string (cdr sb))))))
		      (princ "(") (print-mod-name (car sb)
						  *standard-output*
						  t
						  t)
		      (princ ")"))))))
	    (print-next)
	    (princ "}")))
	;; SIGNATURE
	(let ((sorts (sorts-to-be-shown mod *chaos-verbose*))
	      (opinfos (ops-to-be-shown mod *chaos-verbose*)))
	  (when (or sorts opinfos)
	    (print-next)
	    (princ "signature {")
	    (let ((*print-indent* (+ 2 *print-indent*)))
	      ;; SORTS
	      (when sorts
		(let ((hidden (remove-if-not #'(lambda (x)
						 (sort-is-hidden x))
					     sorts))
		      (visible (remove-if #'(lambda (x)
					      (sort-is-hidden x))
					  sorts)))
		  (when hidden
		    (print-next)
		    ;; (princ "hidden [ ")
		    (princ "*[ ")
		    (let ((*print-indent* (+ 8 *print-indent*)))
		      ;; (print-out-sorts hidden mod 'print-sort-name)
		      (do ((ss hidden (cdr ss)))
			  ((null ss))
			(print-out-sort (car ss) mod 'print-sort-name)
			(when (cdr ss) (princ ",") (print-next)))
		      (princ " ]*")))
		  (when visible
		    (print-next)
		    (let ((*print-indent* (+ 2 *print-indent*)))
		      (princ "[ ")
		      (do ((ss visible (cdr ss)))
			  ((null ss))
			(print-out-sort (car ss) mod 'print-sort-name)
			(when (cdr ss) (princ ",") (print-next)))
		      (princ " ]")))))
	      ;;
	      (when opinfos
		(dolist (op-meth opinfos)
		  (print-op-meth op-meth mod *chaos-verbose*))))
	    (print-next)
	    (princ "}")))
	;; AXIOMS
	(when (or *chaos-verbose*
		  *print-all-eqns*
		  (module-equations mod)
		  (module-rules mod))
	  (print-next)
	  (princ "axioms {")
	  (let ((*print-indent* (+ 2 *print-indent*)))
	    (when (module-variables mod)
	      (dolist (v (reverse (module-variables mod)))
		(print-next)
		(if (term-is-variable? (cdr v))
		    (princ "var ")
		  (princ "pvar "))
		(princ (string (variable-name (cdr v))))
		(princ " : ")
		(print-sort-name (variable-sort (cdr v)) mod)))
	    (if (module-is-ready-for-rewriting mod)
		(if (not (or *chaos-verbose* *print-all-eqns*))
		    (dolist (r (append (reverse (module-equations mod))
				       (reverse (module-rules mod))))
		      (print-next)
		      (print-axiom-brief r) (princ " .")
		      #||
		      (dolist (er (!axiom-A-extensions r))
			(when er (print-next) (print-axiom-brief er) (princ " .")))
		      (dolist (er (!axiom-AC-extension r))
			(when er (print-next) (print-axiom-brief er) (princ " .")))
		      ||#
		      (dolist (er (axiom-extensions r))
			(when er (print-next) (print-axiom-brief er) (princ " .")))
		      )
		    ;; 
		    (dolist (r (get-module-axioms mod t))
		      (print-next)
		      (print-axiom-brief r) (princ " .")
		      #||
		      (dolist (er (!axiom-A-extensions r))
			(when er (print-next) (print-axiom-brief er) (princ " .")))
		      (dolist (er (!axiom-AC-extension r))
			(when er (print-next) (print-axiom-brief er) (princ " .")))
		      ||#
		      (dolist (er (axiom-extensions r))
			(when er (print-next) (print-axiom-brief er) (princ " .")))
		      ))))
	  (print-next)
	  (princ "}"))
	;; done
	)
      (print-next)
      (princ "}")
      (fresh-line)
      (flush-all)
      (values))))
	 
(defun show-module-in-chaos-syntax (mod)
  (with-in-module (mod)
    (let ((*print-pretty* t))
      (format t "~&~s" (object-decl-form mod)))))

;;; PRINT-MODULE-SORTS
;;;-----------------------------------------------------------------------------
(defun sorts-to-be-shown (mod &optional all)
  (let ((sorts (if all (module-all-sorts mod)
		   (module-sorts mod))))
    (if (or (module-is-hard-wired mod)
	    (module-is-system-module mod))
	sorts
	(filter-hard-sorts sorts))))

(defun print-module-sorts (mod &optional describe all)
  (with-in-module (mod)
    (let ((sorts (reverse (sorts-to-be-shown mod all))))
      (cond ((not describe)
	     (when (module-principal-sort mod)
	       (print-next)
	       (princ "* principal sort : ")
	       (print-out-sorts (list (module-principal-sort mod)) mod
				'print-sort-name))
	     (let ((hidden (remove-if-not #'(lambda (x) (sort-is-hidden x)) sorts))
		   (visible (remove-if #'(lambda (x) (sort-is-hidden x)) sorts)))
	       (when hidden
		 (print-next)
		 (princ "* hidden sorts :")
		 (let ((*print-indent* (+ *print-indent* 2)))
		   (print-next)
		   (print-out-sorts hidden mod 'print-sort-name)))
	       (when visible
		 (print-next)
		 (princ "* visible sorts :")
		 (let ((*print-indent* (+ *print-indent* 2)))
		   (print-next)
		   (print-out-sorts visible mod 'print-sort-name)))))
	    ;; 
	    (t				; describe
	     (dolist (s sorts)
	       (print-next)
	       (princ "----------------------------------------------------------------------")
	       (print-next)
	       (describe-sort s)))))
    (flush-all)))

(defun print-out-sorts (sort-list mod &optional (printer 'print-sort-name))
  (do ((ss sort-list (cdr ss)))
      ((null ss))
    (print-out-sort (car ss) mod printer)
    (when (cdr ss) (print-next))))

(defun print-out-sort (s mod printer)
  (let ((subs (direct-subsorts s))
	(sups (direct-supersorts-no-err s)))
    (funcall printer s mod)
    (when (or subs sups)
      (let ((*print-indent* (+ 2 *print-indent*)))
	(princ ", ")
	(dolist (sub subs)
	  (funcall printer sub mod)
	  (princ " "))
	(when subs (princ "< "))
	(funcall printer s mod)
	(when sups
	  (princ " <")
	  (dolist (super sups)
	    (princ " ")
	    (funcall printer super mod)))))
    ))

;;; PRINT-MODULE-OPS
;;;-----------------------------------------------------------------------------
(defun module-own-op-methods (mod)
  (let ((res nil))
    (with-in-module (mod)
      (dolist (opinfo (reverse (module-all-operators mod)))
	(let ((meth nil))
	  (dolist (m (opinfo-methods opinfo))
	    (when (and (eq (method-module m) mod)
		       (or (not (method-is-error-method m))
			   (method-is-user-defined-error-method m)))
	      (push m meth)))
	  (when meth
	    (push (list (opinfo-operator opinfo) meth) res))))
      (nreverse res))))
	   
(defun ops-to-be-shown (mod &optional all)
  (let ((ops (if all
		 (reverse (module-all-operators mod))
		 (module-own-op-methods mod))))
    (if (module-is-hard-wired mod)
	ops
	(filter-hard-opinfos ops))))
    
(defun print-module-ops (mod &optional describe all)
  (with-in-module (mod)
    (let ((ops (ops-to-be-shown mod all)))
      (dolist (opinfo ops)
	(if describe
	    (describe-operator opinfo)
	    (progn
	      (print-next)
	      (describe-operator-brief opinfo)))))))

;;; PRINT-MODULE-EQS
;;;-----------------------------------------------------------------------------
(defun print-module-eqs (mod &optional describe)
  (with-in-module (mod)
    (when (module-equations mod)
      (princ "equations : ")
      (let ((*print-indent* (+ 2 *print-indent*)))
	(dolist (r (module-equations mod))
	  (print-next)
	  (if describe
	      (print-rule r)
	      (print-axiom-brief r)))))))

;;; PRINT-MODULE-RLS
;;;-----------------------------------------------------------------------------
(defun print-module-rls (mod &optional describe)
  (with-in-module (mod)
    (when (module-rules mod)
      (princ "rules : ")
      (let ((*print-indent* (+ 2 *print-indent*)))
	(dolist (r (module-rules mod))
	  (if describe
	      (print-rule r)
	      (print-axiom-brief r)))))))

;;; PRINT-MODULE-AXS
;;;-----------------------------------------------------------------------------
(defun print-module-axs (mod &optional describe)
  (with-in-module (mod)
    (let ((own-axs (module-own-axioms-ordered mod nil))
	  (imp-axs (if (or *print-all-eqns* *module-all-rules-every*)
		       (module-imported-axioms mod nil)
		       nil))
	  (flg1 nil)
	  (flg2 nil)
	  (*print-indent* (+ 2 *print-indent*)))
      (dolist (ax own-axs)
	(if (and (null flg1) (memq (axiom-type ax) '(:equation
						     :pignose-axiom
						     :pignose-goal)))
	    (progn
	      (decf *print-indent* 2)
	      (format t "~&- Equations")
	      (incf *print-indent* 2)
	      (setq flg1 t))
	  (if (and (null flg2) (eq (axiom-type ax) :rule))
	      (progn
		(decf *print-indent* 2)
		(format t "~&- Transitions")
		(incf *print-indent* 2)
		(setq flg2 t))))
	(print-next)
	(if describe
	    (print-rule ax)
	    (print-axiom-brief ax)))
      (when imp-axs
	(decf *print-indent* 2)
	(format t "~&- Imported axioms")
	(incf *print-indent* 2)
	(dolist (ax imp-axs)
	  (print-next)
	  (if describe
	      (print-rule ax)
	      (print-axiom-brief ax))))
      )))

;;; PRINT-MODULE-RULES
;;;-----------------------------------------------------------------------------
(defun print-module-rules (mod &optional describe)
  (with-in-module (mod)
    (dolist (r (module-rewrite-rules mod))
      (print-next)
      (if describe 
	  (print-rule r)
	  (print-axiom-brief r)))))

;;; PRINT-MODULE-SUBMODUES
;;;-----------------------------------------------------------------------------
(defun get-non-parameter-submodules (mod)
  (with-in-module (mod)
    (let ((skip (mapcar #'cdar (module-parameters mod)))
	  (res nil))
      (if (print-merged mod)
	  (push *open-module* skip))
      (dolist (sb (module-submodules mod))
	(unless (member (car sb) skip)
	  (push sb res)))
      res)))

(defun print-submodule-list (subs &optional describe)
  (declare (ignore describe))
  (dolist (sb subs)
    (print-next)
    (format t "~a (" (string-downcase (string (cdr sb))))
    (let ((*print-indent* (+ 2 *print-indent*)))
      (print-mod-name (car sb) *standard-output* t t))
    (princ ")")))

(defun print-module-submodules (mod &optional describe)
  (declare (ignore describe))
  (dolist (sb (get-non-parameter-submodules mod))
    (print-next)
    (if (eq :using (cdr sb))
	(format t "-- ~a(" (string-downcase (string (cdr sb))))
	(format t "~a(" (string-downcase (string (cdr sb)))))
    (let ((*print-indent* (+ 2 *print-indent*)))
      (print-mod-name (car sb) *standard-output* nil t))
    (princ ")")))

;;; PRINT-MODULE-PARAMETERS
;;;-----------------------------------------------------------------------------
(defun print-module-parameters (mod &optional
				    (stream *standard-output*)
				    (abbrev t))
  (declare (ignore abbrev))
  (with-in-module (mod)
    (let ((params (get-module-parameters mod)))
      (if params
	  (progn
	    (print-next)
	    (let ((flag nil))
	      (dolist (x params)
		(let ((arg-name (parameter-arg-name x))
		      (cntxt (parameter-context x)))
		  (if flag (print-next) (setq flag t))
		  (if (or (null cntxt)
			  (eq mod cntxt))
		      (format t "* argument ~a : " arg-name)
		      (progn
			(format t "* argument ~a." arg-name)
			(print-mod-name cntxt stream t t)
			(princ " : ")))
		  (princ (string-downcase (string (parameter-imported-mode x))))
		  (princ " ")
		  (force-output)
		  (print-parameter-theory-name (parameter-theory-module x)
					       stream
					       nil
					       :no-param)))))
	  (princ "NONE.")))
    (print-next)))


;;; PRINT-MODULE-SORT
;;;-----------------------------------------------------------------------------
(defun print-module-sort (mod srt &optional describe)
  (with-in-module (mod)
    (if describe
	(describe-sort srt)
	(print-sort-name srt mod))))

;;; PRINT-MODULE-VARIABLES
;;;-----------------------------------------------------------------------------
(defun print-module-variables (mod &optional describe)
  (declare (ignore describe))
  (with-in-module (mod)
    (when (module-variables mod)
      (dolist (v (mapcar #'cdr (reverse (module-variables mod))))
	(if (term-is-variable? v)
	    (princ "var ")
	  (princ "pvar "))
	(princ (string (variable-name v)))
	(princ " : ")
	(print-sort-name (variable-sort v) mod)
	(print-next)))))

;;; EOF

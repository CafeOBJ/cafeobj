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
(in-package :chaos)
#|=============================================================================
			     System:CHAOS
			     Module:psup
			    File:psup.lisp
=============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))


;;; PROOF SUPPORT SYSTEM INTERFACE ============================================

;;; service routines for proof support system
;;; experimental implementation. syntax of output forms must be fixed soon.
;;;

;;;
;;; special error handler ------------------------------
;;; 
(defmacro with-logging-error (&body body)
  ` (let ((res nil))
      (with-output-to-string (str)
	(let ((*error-output* str)
	      (*suppress-err-handler-msg* t)
	      (val nil))
	  (ignoring-chaos-error
	   (setq val (progn ,@body)))
	  (if val
	      (setq res (list t val))
	      (setq res (list nil (get-output-stream-string str))))))
      res))

;;;
;;; PSUP-GET-IMPORT-GRAPH
;;;
(defun psup-get-import-graph (&optional modexp)
  (let ((*print-circle* nil)
	(*print-case* :downcase)
	(*print-escape* nil))
    (prin1
     (with-logging-error
	 (let ((modval (trs-get-mod-or-error modexp)))
	   (psup-get-import-graph* modval))))))
	    
(defun psup-get-import-graph* (module)
  (let* ((subs (module-all-submodules module))
	 (res nil)
	 (mod-name-list
	  (nconc (list (cons module (make-module-print-name2 module)))
		 (mapcar #'(lambda (x)
			     (cons (car x) (make-module-print-name2 (car x))))
			 subs))))
    (dolist (sub (module-direct-submodules module))
      (push (list (cdr sub) (cdr (assq module mod-name-list))
		  (cdr (assq (car sub) mod-name-list)))
	    res))
    (dolist (m (mapcar #'car subs))
      (dolist (sub (module-direct-submodules m))
	(push (list (cdr sub) (cdr (assq m mod-name-list))
		    (cdr (assq (car sub) mod-name-list)))
	      res)))
    (nreverse res)))

;;;
;;; PSUP-GET-SORT-GRAPH
;;;
(defun psup-get-sort-graph (&optional modexp)
  (let ((*print-circle* nil)
	(*print-case* :downcase)
	(*print-escape* nil))
    (prin1
     (with-logging-error
	 (psup-get-sort-graph* (get-module-trs-or-error modexp))))
    (values)))

(defun psup-make-sort-info (sort trs)
  (string (cdr (assq sort (trs$sort-name-map trs)))))

(defun psup-get-module-sorts (trs)
  (let ((sorts nil)
	(snmap (trs$sort-name-map trs)))
    (dolist (s snmap)
      (unless (err-sort-p (car s))
	(push (string (cdr s)) sorts)))
    sorts))

(defun psup-get-sort-graph* (trs)
  (let ((sgraph (trs$sort-graph trs))
	(errgraph (trs$err-sorts trs)))
    (list (psup-get-module-sorts trs)
	  (mapcar #'(lambda (x)
		      (list (string (car x))
			    (string (cadr x))))
		  sgraph)
	  (mapcar #'(lambda (x)
		      (list (string (car x))
			    (string (cadr x))))
		  errgraph))))

;;;
;;; PSUP-GET-OPERATORS
;;;
(defun psup-get-operators (&optional modexp)
  (let ((*print-circle* nil)
	(*print-case* :downcase)
	(*print-escape* nil))
    (prin1
     (with-logging-error
	 (psup-get-operators* (get-module-trs-or-error modexp))))
    (values)))

(defun psup-get-operators* (trs)
  (let ((res nil))
    (dolist (info (trs$op-info-map trs))
      (push (psup-make-method-info (cdr info) trs) res))
    (dolist (info (trs$sem-relations trs))
      (push (psup-make-method-info (cdr info) trs) res))
    res))

(defun psup-make-method-info (minfo trs)
  (list* (string (car minfo))
	 (mapcar #'string (cadr minfo))
	 (string (caddr minfo))
	 (let ((attrs nil))
	   (dolist (attr (nthcdr 3 minfo) (nreverse attrs))
	     (if (consp attr)
		 (if (memq (car attr) '(:id :idr))
		     (push (list (car attr)
				 (trs-term-to-psup-term (cadr attr) trs))
			   attrs)
		     (push attr attrs))
		 (push (list attr) attrs))))
	 ))

(defun psup-map-chaos-op-to-trs (method trs)
  (string (map-chaos-op-to-trs method trs)))

(defun trs-term-to-psup-term (trs-term trs)
  (if trs-term
      (let ((type (car trs-term))
	    (name (cadr trs-term))
	    (sort (caddr trs-term))
	    (subs (nthcdr 3 trs-term)))
	(list* type
	       (if (symbolp name)
		   (string name)
		   name)
	       (string sort)
	       (mapcar #'trs-term-to-psup-term subs trs)))
      nil))

;;;
;;; PSUP-PARSE-EXPRESSION
;;;
(defun psup-parse-expression (modexp expr &rest vars)
  (let ((*print-circle* nil)
	(*print-case* :downcase)
	(*print-escape* nil))
    (prin1
     (with-logging-error
	 (psup-parse-expression* (get-module-trs-or-error modexp)
				 expr
				 vars)))
    (values)))

(defun psup-parse-expression* (trs expr vars
				   &aux (mod (trs$module trs)))
  (with-in-module (mod)
    (let ((*parse-variables* (psup-parse-vars vars mod))
	  (term nil))
      (setq term (simple-parse mod expr))
      (if (term-is-an-error term)
	  (chaos-error 'syntax-error)
	  (psup-make-term-form term trs)))))

(defun psup-parse-vars (vars mod)
  (let ((res nil))
    (dolist (var vars)
      (let* ((decl (parse-with-delimiter var #\space))
	     (names (mapcar #'intern (firstn decl (- (length decl) 2))))
	     (sort (find-sort-in mod (car (last decl)))))
	(unless sort
	  (with-output-chaos-error ('no-such-sort)
	    (format t "no such sort ~a" (car (last decl)))
	    ))
	(dolist (name names)
	  (push (cons name (make-variable-term sort name)) res))))
    (nreverse res)))

;;;
;;; PSUP-PARSE-AXIOM
;;;
(defun psup-parse-axiom (modexp lhs rhs cond &rest vars)
  (let ((*print-circle* nil)
	(*print-case* :downcase)
	(*print-escape* nil))
    (prin1
     (with-logging-error
	 (psup-parse-axiom* (get-module-trs-or-error modexp)
			    lhs
			    rhs
			    cond
			    vars)))
    (values)))

(defun psup-parse-axiom* (trs lhs rhs cond vars
			      &aux (mod (trs$module trs)))
  (with-in-module (mod)
    (let ((*parse-variables* (psup-parse-vars vars mod))
	  (lhs-parse nil)
	  (rhs-parse nil)
	  (cond-parse nil))
      (setq lhs-parse (simple-parse mod lhs))
      (setq rhs-parse (simple-parse mod rhs))
      (when (and cond (not (equal cond "")))
	(setq cond-parse (simple-parse mod cond)))
      (when (or (term-is-an-error lhs-parse)
		(term-is-an-error rhs-parse)
		(if cond-parse
		    (term-is-an-error cond-parse)
		    nil))
	(chaos-error 'syntax-error))
      (list* (psup-make-term-form lhs-parse trs)
	     (psup-make-term-form rhs-parse trs)
	     (if cond-parse
		 (psup-make-term-form cond-parse trs)
		 nil)))))

;;;
;;; PSUP-UNPARSE-EXPRESSION
;;;
(defun psup-unparse-expression (modexp term)
  (let ((*print-circle* nil)
	(*print-case* :downcase)
	(*print-escape* nil))
    (prin1
     (with-logging-error
	 (psup-unparse-expression* (get-module-trs-or-error modexp)
				   term)))
    (values)))

(defun psup-unparse-expression* (trs psup-term)
  (let ((expr (trs-re-make-term-form trs psup-term))
	(vars (trs-term-variables psup-term)))
    (list* expr
	   (if vars
	       (mapcar #'(lambda (x)
			   (psup-re-make-variable-form x))
		       vars)
	       nil))))

(defun psup-re-make-variable-form (x)
  (let ((name (string (trs-term-head x)))
	(sort (string (trs-term-sort x))))
    (let ((dot-pos (position #\. sort)))
      (if dot-pos
	  (setq sort (subseq sort 0 dot-pos)))
      (concatenate 'string name ":" sort))))
;;;
;;; TERM
;;;
(defun psup-make-term-form (term trs)
  (cond ((term-is-simple-lisp-form? term)
	 (list :lisp (lisp-form-original-form term)))
	((term-is-general-lisp-form? term)
	 (list :glisp (lisp-form-original-form term)))
	((term-is-builtin-constant? term)
	 (list :builtin-value
	       (term-builtin-value term)
	       (psup-make-sort-info (term-sort term) trs)))
	((term-is-variable? term)
	 (list :var (string (variable-name term))
	       (psup-make-sort-info (variable-sort term) trs)))
	((term-is-applform? term)
	 (list* :op
		(psup-map-chaos-op-to-trs (term-head term) trs)
		(psup-make-sort-info (term-sort term) trs)
		(mapcar #'(lambda (x)
			    (psup-make-term-form x trs))
			(term-subterms term))))
	(t (with-output-panic-message ()
	     (format t "unknown term : ")
	     (term-print term)))))

(defun trs-term-to-psup (term)
  (case (trs-term-type term)
    (:lisp term)
    (:glisp term)
    (:var ` (:var ,(string (trs-term-head term))
		  ,(string (trs-term-sort term))))
    (:builtin-value
     ` (:builtin-value ,(trs-term-builtin-value term)
		       ,(string (trs-term-sort term))))
    (:op (list* ':op
		(string (trs-term-head term))
		(string (trs-term-sort term))
		(mapcar #'(lambda (x)
			    (trs-term-to-psup x))
			(trs-term-subterms term)))
	 )
    (otherwise (break))))

;;;
;;; PSUP-GET-AXIOMS
;;;
(defun psup-get-axioms (&optional modexp include-built-in)
  (let ((*print-circle* nil)
	(*print-case* :downcase)
	(*print-escape* nil))
    (prin1
     (with-logging-error
	 (psup-get-axioms* (get-module-trs-or-error modexp)
			   include-built-in )))
    (values)))

(defun psup-get-axioms* (trs include-built-in)
  (let ((axs nil)
	(mod (trs$module trs))
	(eqns nil)
	(*module-all-rules-every* t))
    (with-in-module (mod)
      (let ((own-axs (module-own-axioms-ordered mod nil))
	    (imp-axs (module-imported-axioms mod nil))
	    (sem-axs (trs$sem-axioms trs))
	    val)
	(setq val (trs$get-axioms own-axs trs t))
	(setq eqns (car val))
	(setq val (trs$get-axioms imp-axs trs t))
	(setq eqns (nconc eqns (car val)))
	(setq val (trs$get-axioms sem-axs trs t))
	(setq eqns (nconc eqns (car val)))
	(dolist (x eqns)
	  (when (or (not (trs-axiom-is-built-in x))
		    include-built-in)
	    (push (psup-make-axiom-info x) axs)))
	))
    (nreverse axs)))

(defun psup-make-axiom-info (ax)
  (list* (trs-axiom-type ax)
	 (if (trs-axiom-label ax)
	     (string (trs-axiom-label ax))
	     nil)
	 (trs-term-to-psup (trs-axiom-lhs ax))
	 (trs-term-to-psup (trs-axiom-rhs ax))
	 (if (trs-axiom-condition ax)
	     (list (trs-term-to-psup (trs-axiom-condition ax)))
	     nil)))

(defun psup-make-axiom-info2 (ax trs &optional ignore)
  (declare (ignore ignore))
  (psup-make-axiom-info (get-trs-axiom ax trs t)))

;;;
;;; PSUP-GET-VIEW
;;;

(defun psup-image-of-axioms (&optional view-expr)
  (let ((*print-circle* nil)
	(*print-case* :downcase)
	(*print-escape* nil))
    (prin1
     (with-logging-error
	 (let ((view (find-view-in-env (normalize-modexp view-expr))))
	   (if view
	       (psup-image-of-axioms* view)
	       (with-output-chaos-error ('no-such-view)
		 (format t "no such view \"~a\"" view-expr)
		 )))))))

(defun psup-image-of-axioms* (view)
  (let* ((ax-images (view-get-image-of-axioms view))
	 (target (view-target view))
	 (trs (get-module-trs target)))
    (mapcan #'(lambda (ax) (let ((ax (psup-make-axiom-info2 ax trs t)))
			     (if ax
				 (list ax)
				 nil)))
	    ax-images)))

;;; EOF

;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: gen-eval.lisp,v 1.6 2007-01-27 11:30:39 sawada Exp $
(in-package :chaos)
#|==============================================================================
				 System: CHAOS
				 Module: chaos
			      File: gen-eval.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; ****************************************************************************
;;;			     GENERIC AST EVALUATOR
;;; ****************************************************************************

;;;-- Generic Evaluator --------------------------------------------------------
;;; EVAL-AST : ast -> semantic_object
;;; generic evaluator of ast.
;;;-----------------------------------------------------------------------------
;;; (declaim (special *chaos-eval-context*))
;;; (defvar *chaos-eval-context* nil)
(declaim (special *dribble-ast* *ast-log*))
(defvar *dribble-ast* nil)
(defvar *dribble-stream* nil)
(defvar *ast-log* nil)
(defvar *no-log-parameter* t)
(declaim (special *eval-ast*))
(defvar *eval-ast* t)

(defun ast-to-be-dribbled? (ast)
  (and (chaos-ast? ast)
       (or (eq (ast-category ast) ':chaos-script)
	   (eq (ast-type ast) '%view-decl)
	   (if (eq (ast-type ast) '%module-decl)
	       (or (not *no-log-parameter*)
		   (not (and (consp (%module-decl-name ast))
			     (equal "::" (cadr (%module-decl-name ast))))))
	       (or *open-module*
		   nil)))))

(defun eval-ast (ast &optional (print-result nil))
  (when *dribble-ast*
    (when (ast-to-be-dribbled? ast)
      (when *dribble-stream*
	(write (list 'eval-ast-if-need `',ast) :stream *dribble-stream* :escape t)
	(terpri *dribble-stream*)
	(force-output *dribble-stream*))
      (push ast *ast-log*)))
  ;;
  (when *eval-ast*
    (cond ((chaos-ast? ast)
	   (let ((evaluator (or (ast-evaluator ast)
				(and (fboundp (car ast))
				     (symbol-function (car ast))))))
	     (cond (evaluator
		    (let ((module (or ;; (chaos-eval-context ast)
				   ;; *chaos-eval-context*
				   *current-module*
				   *last-module*)))
		      (when (and module (not (module-p module)))
			(setq module (find-module-in-env
				      (normalize-modexp (string module)))))
		      (if module
			  (if (null *current-module*)
			      (with-in-module (module)
				(prog1 (funcall evaluator ast)
				  ;; (deallocate-ast ast)
				  ))
			      (prog1 (funcall evaluator ast)
				))
			  ;; may cause panic.
			(return-from eval-ast (funcall evaluator ast)))))
		   (t (let ((val (eval-modexp ast)))
			(if (modexp-is-error val)
			    (with-output-chaos-warning ()
			      (format t  "AST evaluator accepted an ast ~s with no evaluator specified."
				      (print-ast ast))
			      (return-from eval-ast ast))) ; returns the ast as is.
			)))))
	  (t ;; evaluate it as lisp form
	   (cond ((symbolp ast)
		  (unless (boundp ast)
		    (format t "~&symbol ~s has no bound value." ast)
		    (return-from eval-ast nil)))
		 ((listp ast)
		  (unless (symbolp (car ast))
		    (format t "~&invalid function application form: ~a" ast)
		    (return-from eval-ast nil))
		  (unless (fboundp (car ast))
		    (format t "~&symbol ~s has no function definition." (car ast))
		    (return-from eval-ast nil))))
	   ;;
	   (let ((res (eval ast)))
	     (when print-result
	       (format t "~&~s" res))
	     (return-from eval-ast res))))))

(defun eval-seq (seq)
  (mapcar #'(lambda (obj) (eval-ast obj))
	  (%seq-args seq)))

(defun eval-ast2 (ast)
  (eval-ast ast)
  )

;;; EOF

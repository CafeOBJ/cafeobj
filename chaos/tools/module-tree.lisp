;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: module-tree.lisp,v 1.1.1.1 2003-06-19 08:29:38 sawada Exp $
(in-package :chaos)
#|==============================================================================
				 System: CHAOS
				 Module: tools
			     File: module-tree.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; MODULE HIERARCHY TREE

(defun make-submodule-tree (mod)
  (mapcar #'(lambda (x)
	      (cons x (make-submodule-tree (car x))))
	  (module-direct-submodules mod)))

(defun make-module-tree (mod)
  (cons (list mod) (make-submodule-tree mod)))

(defun print-module-tree (mod &optional (stream *standard-output*))
  (!print-module-tree mod stream nil))

(defun print-module-graph (mod &optional (stream *standard-output*))
  (when (module-is-inconsistent mod)
    (with-output-chaos-warning ()
      (princ "specified module is inconsistent and cannot be shown.")
      (print-next)
      (princ "please redefine it!")
      (return-from print-module-graph nil)))
  (!print-module-tree mod stream t))

#||
(defun !print-module-tree (mod stream show-as-graph)
  (let* ((leaf? #'(lambda (tree) (null (dag-node-subnodes tree))))
	 (leaf-name #'(lambda (tree)
		       (with-output-to-string (str)
			 (let ((datum (dag-node-datum tree)))
			   (case (cdr datum)
			     (:protecting (princ "pr(" str))
			     (:extending (princ "ex(" str))
			     (:using (princ "us(" str))
			     (:modmorph (princ "!(" str)))
			   (print-chaos-object (car datum) str)
			   (when (cdr datum) (princ ")" str)))
			 str)))
	 (leaf-info #'(lambda (tree) (declare (ignore tree)) t))
	 (int-node-name #'(lambda (tree) (funcall leaf-name tree)))
	 (int-node-children #'(lambda (tree)
				(let ((subs nil))
				  (dolist (sub-node (dag-node-subnodes tree))
				    (let ((datum (dag-node-datum sub-node)))
				      (unless (and (module-p (car datum))
						   (or (memq (car datum) *kernel-hard-wired-builtin-modules*)
						       (memq (cdr datum) '(:view :modmorph))))
					(push sub-node subs))))
				  subs)))) ;; #'(lambda (tree) (dag-node-subnodes tree))
    (force-output stream)
    (print-next nil *print-indent* stream)
    (print-trees (list (if show-as-graph
			   (augment-tree-as-graph (module-dag mod))
			   (augment-tree (module-dag mod))))
		 stream)))
||#

(defun !print-module-tree (mod stream show-as-graph)
  (let* ((leaf? #'(lambda (tree) (null (dag-node-subnodes tree))))
	 (leaf-name #'(lambda (tree)
			(with-output-to-string (str)
			   (let ((datum (dag-node-datum tree)))
			     (case (cdr datum)
			       (:protecting (princ "pr(" str))
			       (:extending (princ "ex(" str))
			       (:using (princ "us(" str))
			       (:modmorph (princ "!(" str)))
			     (print-mod-name-x (car datum) str t nil)
			     (when (cdr datum) (princ ")" str)))
			   str)))
	 (leaf-info #'(lambda (tree) (declare (ignore tree)) t))
	 (int-node-name #'(lambda (tree) (funcall leaf-name tree)))
	 (int-node-children #'(lambda (tree)
				(let ((subs nil))
				  (dolist (sub-node (dag-node-subnodes tree))
				    (let ((datum (dag-node-datum sub-node)))
				      (when (and (module-p (car datum))
						 (not (module-is-parameter-theory
						       (car datum)))
						 (not (memq (car datum)
							    *kernel-hard-wired-builtin-modules*))
						 (not (memq (cdr datum)
							    '(:view :modmorph))))
					(push sub-node subs))))
				  subs)))) ;; #'(lambda (tree) (dag-node-subnodes tree))
    (force-output stream)
    (print-next nil *print-indent* stream)
    (print-trees (list (if show-as-graph
			   (augment-tree-as-graph (module-dag mod))
			   (augment-tree (module-dag mod))))
		 stream)))

;;; MODULE EXPRESSION TREE

(defun get-modexp-children (modexp)
  (cond ((chaos-ast? modexp)
	 (case (ast-type modexp)
	   ((%ren-sort %ren-op %ren-var %ren-param %+)
	    (remove nil (third modexp)))
	   (%rmap nil)
	   (%! (remove nil `(,(%instantiation-module modexp)
			     ,@(%instantiation-args modexp))))
	   ((%view %view-from)
	    (remove-if #'(lambda (x) (or (eq x 'none) (null x))) (cdr modexp)))
	   (otherwise (remove nil (cdr modexp)))))
	(t nil)))

(defun print-modexp-tree (modexp &optional (stream *standard-output*))
  (let* ((leaf? #'(lambda (tree) (or (%is-rmap tree) (not (chaos-ast? tree)))))
	 (leaf-name #'(lambda (tree)
			(cond ((chaos-ast? tree)
			       (case (ast-type tree)
				 (%! "_[_]")
				 (%!arg "_<=_")
				 (%* "_*_")
				 (%+ "_+_")
				 ((%view %view-from) "view_")
				 (%rmap "{_}")
				 (%ren-sort "sort_->_")
				 (%ren-op "op_->_")
				 (%ren-param "param_->_")
				 (otherwise "??")))
			      ((and (consp tree) (eq (car tree) ':?name))
			       (cdr tree))
			      ((and (consp tree) (null (cdr tree)))
			       (car tree))
			      (t tree))))
	 (leaf-info #'(lambda (tree) (declare (ignore tree)) t))
	 (int-node-name #'(lambda (tree) (funcall leaf-name tree)))
	 (int-node-children #'get-modexp-children))
    (force-output stream)
    (print-next nil *print-indent* stream)
    (print-trees (list (augment-tree modexp)) stream)))

;;;
;;;
(defun print-subs-list (module)
  (dag-dfs (module-dag module)
	   #'(lambda (node)
	       (let* ((datum (dag-node-datum node))
		      (mode (cdr datum))
		      (mod (car datum)))
		 (format t "~&* mode  :~a" mode)
		 (print-next)
		 (princ " module : ")
		 (print-chaos-object mod)))))

(defun print-mod-name-x (arg &optional
			   (stream *standard-output*)
			   (abbrev nil)
			   (no-param nil))
  (declare (values t))
  (let ((*standard-output* stream))
    (if (module-p arg)
	(let ((modname (get-module-print-name arg)))
	  (if (is-dummy-module arg)
	      (let ((info (getf (module-infos arg) 'rename-mod)))
		(print-mod-name-x (car info) stream abbrev no-param)
		(princ "*DUMMY"))
	      (print-mod-name-internal-x modname abbrev t))
	  (let ((params (get-module-parameters arg)))
	    (when (and params (not no-param))
	      (let ((flg nil))
		;; (princ "[")
		(princ "(")
		(dolist (param params)
		  (let ((theory (parameter-theory-module param)))
		    (if flg (princ ", "))
		    (if (or (null (parameter-context param))
			    (eq arg (parameter-context param)))
			(princ (parameter-arg-name param))
			(progn
			  ;; (format t "~a@" (parameter-arg-name param))
			  (format t "~a." (parameter-arg-name param))
			  (print-mod-name-x (parameter-context param)
					    stream
					    abbrev
					    t)))
		    ;; patch-begin
		    (princ "::")
		    ;; (print-mod-name-x theory stream abbrev t)
		    (print-parameter-theory-name theory stream :abbrev :no-param)
		    ;; patch-end
		    (setq flg t)))
		;; (princ "]")
		(princ ")")
		))))
	(print-chaos-object arg)
	)))

(defun print-mod-name-internal-x (val abbrev
				    &optional
				    (no-param nil))
  (declare (values t))
  (if (stringp val)
      (princ val)
      (if (and (consp val) (not (chaos-ast? val)))
	  (if (equal "::" (cadr val))
	      ;; parameter theory
	      (if abbrev
		  (progn
		    (format t "~a" (car val))
		    (princ ".")
		    (print-mod-name-x (car (last val))
				      *standard-output*
				      abbrev no-param)
		    )
		  ;;
		  (let ((cntxt (fourth val)))
		    (if (and cntxt
			     (not (eq *current-module* cntxt)))
			(progn (format t "~a." (car val))
			       (print-mod-name-x cntxt *standard-output* t t)
			       (princ "::"))
			(format t "~a::" (car val)))
		    (print-mod-name-x (caddr val) *standard-output* nil t)))
	      (print-chaos-object val))
	  (print-modexp val *standard-output* abbrev no-param))))

;;; EOF

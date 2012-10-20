;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: import-tree.lisp,v 1.1.1.1 2003-06-19 08:29:37 sawada Exp $
(in-package :chaos)

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
				      (when (and (module-p (car datum))
						 (not (module-is-parameter-theory
						       (car datum)))
						 (not (memq (car datum)
							    *kernel-hard-wired-builtin-modules*))
						 (not (memq (cdr datum) '(:view :modmorph))))
					(push sub-node subs))))
				  subs)))) ;; #'(lambda (tree) (dag-node-subnodes tree))
    (force-output stream)
    (print-next nil *print-indent* stream)
    (print-trees (list (if show-as-graph
			   (augment-tree-as-graph (module-dag mod))
			   (augment-tree (module-dag mod))))
		 stream)))
;;;
;;; from print-object.lisp
;;;
(defun print-module-internal (module &optional (stream *standard-output*))
  (print-mod-name module stream t nil))

(defun print-mod-name (arg &optional
			   (stream *standard-output*)
			   (abbrev nil)
			   (no-param nil))
  (declare (values t))
  (let ((*standard-output* stream))
    (if (module-p arg)
	(let ((modname (get-module-print-name arg)))
	  (if (is-dummy-module arg)
	      (let ((info (getf (module-infos arg) 'rename-mod)))
		(print-mod-name (car info) stream abbrev no-param)
		(princ "*DUMMY"))
	      (print-mod-name-internal modname abbrev t))
	  (let ((params (get-module-parameters arg)))
	    (when (and params (not no-param))
	      (let ((flg nil))
		;; (princ "[")
		(princ "(")
		(dolist (param params)
		  (let ((theory (parameter-module-theory
				 (parameter-theory-module param))))
		    (if flg (princ ", "))
		    (if (eq arg (parameter-context param))
			(princ (parameter-arg-name param))
			(progn
			  ;; (format t "~a@" (parameter-arg-name param))
			  (format t "~a." (parameter-arg-name param))
			  (print-mod-name (parameter-context param)
					  stream
					  abbrev
					  t)))
		    ;; patch-begin
		    (princ "::")
		    (print-mod-name theory stream abbrev t)
		    ;; patch-end
		    (setq flg t)))
		;; (princ "]")
		(princ ")")
		))))
	(print-chaos-object arg)
	)))

(defun print-mod-name-internal (val abbrev
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
		    (print-mod-name (car (last val))
				    *standard-output*
				    abbrev no-param)
		    )
		  ;;
		  (let ((cntxt (fourth val)))
		    (if (and cntxt
			     (not (eq *current-module* cntxt)))
			(progn (format t "~a." (car val))
			       (print-mod-name cntxt *standard-output* t t)
			       (princ "::"))
			(format t "~a::" (car val)))
		    (print-mod-name (caddr val) *standard-output* nil t)))
	      (print-chaos-object val))
	  (print-modexp val *standard-output* abbrev no-param))))

(defun print-simple-mod-name (module &optional (stream *standard-output*))
  (if (and *open-module*
	   (equal "%" (get-module-print-name module)))
      (progn
	(princ "%" stream)
	(print-mod-name *open-module* stream t nil))
      (print-mod-name module stream t nil)))

(defun make-module-print-name2 (mod)
  (with-output-to-string (name-string)
    (print-mod-name2 mod name-string t)
    name-string))

(defun print-mod-name2 (arg &optional
			    (stream *standard-output*)
			    (no-param nil))
  (let ((*standard-output* stream))
    (if (module-p arg)
	(let ((modname (get-module-print-name arg)))
	  (if (is-dummy-module arg)
	      (let ((info (getf (module-infos arg) 'rename-mod)))
		(print-mod-name2 (car info) stream no-param)
		(princ "*DUMMY"))
	      (print-mod-name-internal2 modname no-param))
	  (let ((params (get-module-parameters arg)))
	    (when (and params (not no-param))
	      (let ((flg nil))
		(princ "(")
		(dolist (param params)
		  (let ((real-theory (parameter-theory-module param)))
		    (declare (ignore real-theory)) ; ***
		    (if flg (princ ", "))
		    (if (eq arg (parameter-context param))
			(princ (parameter-arg-name param))
			(progn
			  (format t "~a." (parameter-arg-name param))
			  (print-mod-name2 (parameter-context param)
					   stream
					   t)))
		    (setq flg t)))
		(princ ")")
		))))
	;; unknown object ...
	(print-chaos-object arg)
	)))

(defun print-mod-name-internal2 (val &optional (no-param nil))
  (if (stringp val)
      (princ val)
      (if (and (consp val) (not (chaos-ast? val)))
	  (if (equal "::" (cadr val))
	      ;; parameter theory
	      (progn
		(format t "~a." (car val))
		(print-mod-name2 (car (last val))
				 *standard-output*
				 no-param))
	      (print-chaos-object val))
	  (print-modexp val *standard-output* nil no-param))))

;;; EOF

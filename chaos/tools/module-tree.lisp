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

(defun !print-module-tree (mod stream show-as-graph)
  (let* ((leaf? #'(lambda (tree) (null (dag-node-subnodes tree))))
	 (leaf-name #'(lambda (tree)
			(with-output-to-string (str)
			   (let ((datum (dag-node-datum tree)))
			     (case (cdr datum)
			       (:protecting (princ "pr(" str))
			       (:extending (princ "ex(" str))
			       (:using (princ "us(" str))
			       (:including (princ "inc(" str))
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
  (let ((*standard-output* stream))
    (if (module-p arg)
	(let ((modname (get-module-print-name arg)))
	  (if (is-dummy-module arg)
	      (let ((info (getf (module-infos arg) 'rename-mod)))
		(print-mod-name-x (car info) stream abbrev no-param)
		(princ "*DUMMY"))
	    (with-in-module (arg)
	      (print-mod-name-internal-x modname abbrev t)))
	  (let ((params (get-module-parameters arg)))
	    (when (and params (not no-param))
	      (let ((flg nil))
		(princ "[")
		;; (princ "(")
		(dolist (param params)
		  (let ((theory (parameter-theory-module param)))
		    (if flg (princ ", "))
		    (if (or (null (parameter-context param))
			    (eq arg (parameter-context param)))
			(princ (parameter-arg-name param))
		      (if (not (eq (parameter-context param) arg))
			  (progn
			    (format t "~a." (parameter-arg-name param))
			    (print-mod-name-x (parameter-context param)
					      stream
					      abbrev
					      t))
			(format t "~a" (parameter-arg-name param))))
		    ;; patch-begin
		    (princ "::")
		    (print-parameter-theory-name theory stream :abbrev :no-param)
		    (setq flg t)))
		(princ "]")
		;; (princ ")")
		))))
	(print-chaos-object arg))))

(defun print-mod-name-internal-x (val abbrev &optional (no-param nil))
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
		  (print-mod-name-x (car (last val)) *standard-output* abbrev no-param))
	      (let ((cntxt (fourth val)))
		(if (and cntxt
			 (not (eq *current-module* cntxt)))
		    (progn (format t "~a." (car val))
			   (print-mod-name-x cntxt *standard-output* t t)
			   (princ "::"))
		  (format t "~a::" (car val)))
		(print-mod-name-x (caddr val) *standard-output* abbrev t)))
	  (print-chaos-object val))
      (print-modexp val *standard-output* abbrev no-param))))

(defvar .mod-dup-hash. (make-hash-table :test #'eq))

(defun describe-module-tree (dag-node &optional (stream *standard-output*))
  (clrhash .mod-dup-hash.)
  (d-module-tree* dag-node stream nil))

(defun describe-module-graph (dag-node &optional (stream *standard-output*))
  (clrhash .mod-dup-hash.)
  (d-module-tree* dag-node stream nil))

(defun pr-imp-mode (mode stream)
  (case mode
    (:protecting (princ "pr" stream))
    (:extending (princ "ex" stream))
    (:using (princ "us" stream))
    (:icluding (princ "inc" stream))
    (:modmorph (princ "!" stream))
    (otherwise (princ "??" stream))))

(defun mod-name-is-parameter (name)
  (and (consp name)
       (not (chaos-ast? name))
       (equal "::" (second name))))

(defun d-module-tree* (dag-node stream p-label &optional my-num)
  (let* ((mod+imp (dag-node-datum dag-node))
	 (mod (car mod+imp))
	 (imp (cdr mod+imp))
	 (*print-line-limit* 100)
	 (*print-xmode* :fancy)
	 (num (if (and p-label my-num)
		  (format nil "~a-~d" p-label my-num)
		(if my-num
		    (format nil "~a" my-num)
		  nil)))
	 (dup? (gethash mod .mod-dup-hash.)))
    (when num
      (format stream "~a: " num)
      (when imp
	(pr-imp-mode imp stream)))
    (unless dup? (setf (gethash mod .mod-dup-hash.) num))
    (let ((*print-indent* (+ 2 *print-indent*)))
      (when num (princ "(" stream))
      (print-mod-name mod *standard-output* t t)
      (when num (princ ")" stream))
      (if dup? (princ "*" stream)
	(with-in-module (mod)
	  (let ((subnodes (dag-node-subnodes dag-node)))
	    (when subnodes
	      (let ((y-num 1))
		(dolist (sub subnodes)
		  (let ((subm (car (dag-node-datum sub)))
			(sub-imp (cdr (dag-node-datum sub))))
		    (when (or *chaos-verbose*
			      (and (not (module-hidden subm))
				   (not (module-is-parameter-theory subm))
				   (not (eq sub-imp :modmorph))))
		      (print-next-prefix #\Space)
		      (d-module-tree* sub stream num y-num)
		      (incf y-num))))))))))))
;;; EOF

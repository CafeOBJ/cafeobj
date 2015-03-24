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
			      File: sort-tree.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

(defun make-module-sort-tree (mod)
  (prepare-for-parsing mod)
  (let* ((sorder (module-sort-order mod))
	 (kinds (get-kinds sorder))
	 (sls (module-sort-relations mod)))
    (labels ((make-tree (s)
	       (let ((sl (assq s sls)))
		 (if sl
		     (cons s (mapcar #'(lambda (x) (make-tree x))
				     (maximal-sorts (_subsorts sl) sorder)))
		     (list s)))))
      (mapc #'(lambda (k)
		(setf (cdr k)
		      (maximal-sorts (cdr k) sorder)))
	    kinds)
      (mapc #'(lambda (k)
		(setf (cdr k)
		      (mapcar #'(lambda (x) (make-tree x))
			      (cdr k))))
	    kinds)
      kinds)))

(defun make-sort-tree (sort &optional (mod (get-object-context sort)))
  (let* ((so (module-sort-order mod))
	 (kind (the-err-sort sort so))
	 (sls (module-sort-relations mod))
	 (fam (maximal-sorts (get-family kind so) so)))
    (labels ((make-tree (s)
	       (let ((sl (assq s sls)))
		 (if sl
		     (cons s (mapcar #'(lambda (x) (make-tree x))
				     (maximal-sorts (_subsorts sl) so)))
		     (list s)))))
      (cons kind 
	    (mapcar #'(lambda (x) (make-tree x)) fam)))))

;;; PRINT-SORT-TREE

(defun print-sort-tree (sort &optional
			     (stream *standard-output*)
			     (mod (get-object-context sort)))
  (!print-sort-tree sort stream mod nil))

(defun print-sort-graph (sort &optional
			      (stream *standard-output*)
			      (mod (get-object-context sort)))
  (!print-sort-tree sort stream mod t))

(defun !print-sort-tree (sort stream mod show-as-graph)
  (let* ((leaf? #'(lambda (tree) (null (cdr tree))))
	 (leaf-name #'(lambda (tree)
			(with-output-to-string (str)
			  (print-sort-name (car tree) mod str)
			  str)))
	 (leaf-info #'(lambda (tree) (declare (ignore tree)) t))
	 (int-node-name #'(lambda (tree)
			    (funcall leaf-name tree)))
	 (int-node-children #'(lambda (tree) (cdr tree))))
    (force-output stream)
    (print-next nil *print-indent* stream)
    (print-trees (list (if show-as-graph
			   (augment-tree-as-graph (make-sort-tree sort mod))
			   (augment-tree (make-sort-tree sort mod))))
		 stream)))

;;; PRINT-MODULE-SORT-TREE

(defun print-module-sort-tree (&optional (mod (get-context-module))
					 (stream *standard-output*))
  (!print-module-sort-tree mod stream nil))

(defun print-module-sort-graph (&optional (mod (get-context-module))
					  (stream *standard-output*))
  (!print-module-sort-tree mod stream t))

(defun !print-module-sort-tree (mod stream show-as-graph)
  (let* ((leaf? #'(lambda (tree) (null (cdr tree))))
	 (leaf-name #'(lambda (tree)
			(with-output-to-string (str)
			  (print-sort-name (car tree) mod str)
			  str)))
	 (leaf-info #'(lambda (tree) (declare (ignore tree)) t))
	 (int-node-name #'(lambda (tree)
			    (funcall leaf-name tree)))
	 (int-node-children #'(lambda (tree) (cdr tree))))
    (dolist (tree (make-module-sort-tree mod))
      (force-output stream)
      (print-next nil *print-indent* stream)
      (princ "------------------------------------------------------------")
      (print-next nil *print-indent* stream)
      (print-trees (list (if show-as-graph
			     (augment-tree-as-graph tree)
			     (augment-tree tree)))
		   stream))))

;;; EOF

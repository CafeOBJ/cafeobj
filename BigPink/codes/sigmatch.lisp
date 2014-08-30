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
			   File:sigmatch.lisp
=============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;;
;;;			SIGNATURE MATCHER
;;; NOTE: This matcher is NOT generic one. It is specialized for
;;;       matching between behavioural specs:
;;;       assumes that data types (visible sorts) are fixed
;;;       except parameterized sorts.
;;;

(declaim (type fixnum .sigmatch-view-num.))
(defvar .sigmatch-view-num. 0)

(defun make-sigmatch-view-name ()
  (declare (values simple-string))
  (format nil "V#~d" (incf .sigmatch-view-num.)))

(defun reset-sigmatch-view-name ()
  (declare (values fixnum))
  (setq .sigmatch-view-num. 0))

;;;
(defstruct (sigmatch-set)
  (module nil :type (or null module))
  (sort nil :type (or null sort*))
  (methods nil :type list)
  (attributes nil :type list)
  (consts nil :type list)
  (ops nil :type list)
  )

(defun sigmatch-set-all-ops (sst)
  (declare (type sigmatch-set sst)
	   (values list))
  (let ((ops nil))
    (dolist (m (sigmatch-set-methods sst))
      (push m ops))
    (dolist (m (sigmatch-set-attributes sst))
      (push m ops))
    (dolist (m (sigmatch-set-consts sst))
      (push m ops))
    (dolist (m (sigmatch-set-ops sst))
      (push m ops))
    ops))

(defun create-sigmatch-set (module)
  (declare (type module module)
	   (values list))
  (with-in-module (module)
    (let ((sorts (module-all-sorts module))
	  (attributes (module-beh-attributes module))
	  (hidden-objects nil))
      (declare (type list sorts attributes hidden-objects))
      (dolist (s sorts)
	(declare (type sort* s))
	(when (and (sort-is-hidden s)
		   (not (or (sort= s *huniversal-sort*)
			    (sort= s *hbottom-sort*))))
	  (push (make-sigmatch-set :sort s :module module)
		hidden-objects)))
      ;;
      (dolist (ho hidden-objects)
	(let* ((hsort (sigmatch-set-sort ho))
	       (ms (get-all-methods-of-sort hsort module)))
	  (declare (type sort* hsort)
		   (type list ms))
	  (dolist (m ms)
	    (declare (type method m))
	    (if (method-is-behavioural m)
		(push m (sigmatch-set-methods ho))
	      (if (and (method-arity m)
		       (memq hsort (method-arity m)))
		  (push m (sigmatch-set-ops ho))
		(push m (sigmatch-set-consts ho)))))
	  (dolist (atr attributes)
	    (declare (type method atr))
	    (when (memq hsort (method-arity atr))
	      (push atr (sigmatch-set-attributes ho))))
	  ))
      ;;
      hidden-objects
      )))

(defun sigmatch (mod1 mod2)
  (declare (type module mod1 mod2))
  (let* ((ss1 (create-sigmatch-set mod1))
	 (ss2 (create-sigmatch-set mod2))
	 ;; (oal nil)
	 (views nil))
    (dolist (s1 ss1)
      (declare (type sigmatch-set s1))
      (dolist (s2 ss2)
	(declare (type sigmatch-set s2))
	(block next
	  (catch 'fail
	    (let ((sal (list (cons (sigmatch-set-sort s1)
				   (sigmatch-set-sort s2))))
		  (sop1 (sigmatch-set-all-ops s1))
		  (sop2 (sigmatch-set-all-ops s2))
		  (omap nil)
		  (ov nil))
	      ;; (declare (type list sal sop1 sop2 omap ov))
	      (when (setq omap (sigmatch-op sop1 sop2 sal))
		(dolist (om omap)
		  (when (setq ov (generate-sigmatch-view mod1 mod2 sal om))
		    (push ov views))))))
	  )))
    views))

(defun sigmatch-op (ms1 ms2 sal)
  (flet ((sort-arity (arity)
	   (sort arity
		 #'(lambda (x y)
		     (string< (string (sort-name x))
			      (string (sort-name y))))))
	 (sort-list-equal (sl1 sl2)
	   (or (equal sl1 sl2)
	       (do ((sl-1 sl1 (cdr sl-1))
		    (sl-2 sl2 (cdr sl-2)))
		   ((or (null sl-1) (null sl-2))
		    (and (null sl-1) (null sl-2)))
		 (unless (eq (sort-name (car sl-1))
			     (sort-name (car sl-2)))
		   (return-from sort-list-equal nil)))
	       ))
	 (sort-equal (s1 s2)
	   (or (eq s1 s2) (eq (sort-name s1) (sort-name s2))))
	 )
    ;;
    (let ((rm nil)
	  (om nil))
    (dolist (m1 ms1)
      (let ((found nil))
	(dolist (m2 ms2)
	  (let ((mp nil))
	    (setq mp (cons m1 m2))
	    (unless (member mp rm :test #'equal)
	      (let ((ar1 nil)
		    (ar2 (sort-arity (copy-list (method-arity m2))))
		    (co1 (or (cdr (assq (method-coarity m1) sal))
			     (method-coarity m1)))
		    (co2 (method-coarity m2))
		    )
		(dolist (s (method-arity m1))
		  (push (or (cdr (assq s sal)) s)
			ar1))
		(setq ar1 (sort-arity ar1))
		#||
		(with-output-msg ()
		  (print-chaos-object mp)
		  (format t "~% ar1 = ~s" ar1)
		  (format t "~% ar2 = ~s" ar2)
		  (format t "~% co1 = ~s" co1)
		  (format t "~% co2 = ~s" co2))
		||#
		(when (and (sort-list-equal ar1 ar2)
			   (sort-equal co1 co2))
		  (setq found t)
		  (push mp rm)
		  (push mp om)
		  (return nil))))))
	;;
	(unless found (throw 'fail :not-found))
	))
    (list om))))

(defun make-sigmatch-op-pat (meth mod &optional vm sal)
  (flet ((find-match-var (sort) 
	   (find-if #'(lambda (x)
			(let ((tsort (or (car (rassoc sort sal))
					 sort)))
			  (eq (sort-name tsort) (sort-name (variable-sort x)))))
		    vm))
	 )
    (with-in-module (mod)
      (let ((vars nil))
	(setq vars (mapcar #'(lambda (x)
			       (let ((var (find-match-var x))
				     (vn nil))
				 (if var
				     (if (sort= (variable-sort var)
						x)
					 var
				       (make-variable-term x
							   (variable-name var)
							   (variable-name var)))
				   (progn
				     (setq vn (gensym "_sm"))
				     (make-variable-term x
							 vn
							 vn)))))
			   (method-arity meth)))
    (make-term-with-sort-check meth vars)))))

(defun generate-sigmatch-view (mod1 mod2 sal oal)
  (let ((smap nil)
	(omap nil)
	(bomap nil)
	(map nil)
	(view nil))
    (dolist (sm sal)
      (push (list (sort-name (car sm)) (sort-name (cdr sm)))
	    smap))
    (dolist (om oal)
      (let ((m1 nil)
	    (vm1 nil)
	    (m2 nil))
	(setq m1 (make-sigmatch-op-pat (car om) mod1))
	(setq vm1 (term-variables m1))
	(setq m2 (make-sigmatch-op-pat (cdr om) mod2 vm1 sal))
	#||
	(setq m1 (method-symbol (car om)))
	(setq m2 (method-symbol (cdr om)))
	||#
	(if (method-is-behavioural (car om))
	    (push (list m1 m2) bomap)
	  (push (list m1 m2) omap))))
    (when smap
      (push (list '%ren-hsort smap) map))
    (when bomap
      (push (list '%ren-bop bomap) map))
    (when omap
      (push (list '%ren-op omap) map))
    (setq view (create-view mod1 mod2 map nil))
    ;; name the view
    (let ((vn (make-sigmatch-view-name)))
      (setf (view-name view) vn)
      (add-depend-relation view :view (view-src view))
      (add-depend-relation view :view (view-target view))
      (add-view-defn vn view)
      (mark-view-as-consistent view)
      vn)))

;;; EoF

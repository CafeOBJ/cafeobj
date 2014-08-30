;;;-*-Mode:LISP; Package: Chaos; Base:10; Syntax:Common-lisp -*-
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
				 System: Chaos
				Module: trs-comp
				File: esort.lisp
===============================================================================|#

;;; ***********
;;; SORT CODING
;;; ***********

;;; SORT-CODING-MAP :
;;; - sort       : sort object
;;; - family-id  : family identifier
;;; - code       : fixnum assigned to a sort-name
;;;                which is a logior sum of own `sort-id-bit' and its lower
;;;                sorts' bit.  
;;; - sort-id-bit: sort identifier (fixnum).

(defun make-sort-coding-map-entry (sort family-id sort-code sort-id-bit)
  (cons sort (list family-id sort-code sort-id-bit)))

(defmacro sort-coding-map-sort (sem) `(car ,sem))
(defmacro sort-coding-map-family-id (sem) `(cadr ,sem))
(defmacro sort-coding-map-sort-code (sem) `(caddr ,sem))
(defmacro sort-coding-map-sort-id-bit (sem) `(cadddr ,sem))

(defmacro get-sort-encoding-entry (sort sem)
  ` (let ((se (assoc ,sort ,sem :test #'eq)))
      (unless se
	(error "get-sort-encoding-entry : no entry for sort!!")
	(print-chaos-object sort))
      se))

(declaim (function sort-to-sort-family-id (t list) fixnum))
(defun sort-to-sort-family-id (sort sem)
  (sort-coding-map-sort-family-id (get-sort-encoding-entry sort sem)))

(declaim (function sort-to-sort-code (t list) fixnum))
(defun sort-to-sort-code (sort sem)
  (sort-coding-map-sort-code (get-sort-encoding-entry sort sem)))

(declaim (function sort-to-sort-id-bit (t list) fixnum))
(defun sort-to-sort-id-bit (sort sem)
  (sort-coding-map-sort-id-bit (get-sort-encoding-entry sort sem)))
	 
(defmacro get-sort-decoding-entry (family-id sort-code sem)
  ` (let ((se (find-if #'(lambda (ee)
			   (and (eql (sort-coding-map-family-id ee)
				     (the fixnum ,family-id))
				(eql (sort-coding-map-sort-code ee)
				     (the fixnum ,sort-code))))
		       ,sem)))
      (unless se
	(error "get-sort-decoding-entry : no for entry for code."))
      se))

(defun sort-code-to-sort (family-id sort-code sem)
  (declare (type fixnum family-id))
  (sort-coding-map-sort (get-sort-decoding-entry family-id sort-code sem)))

;;;
(defun module-error-sorts (module)
  (let ((res nil))
    (maphash #'(lambda (sort sort-relation)
		 (declare (ignore sort))
		 (push-new (_err-sort sort-relation) res))
	     (module-sort-order module))
    res))

;;; module-sort-families
;;; ((error-sort . member-sort .... ) ... )
;;;
(defun module-sort-families (module)
  (let ((res nil))
    (maphash #'(lambda (sort sort-relation)
		 (let ((family (assoc (_err-sort sort-relation) res :test #'eq)))
		   (if family
		       (push sort (cdr family))
		       (push (cons (_err-sort sort-relation) (list sort)) res))))
	     (module-sort-order module))
    res))

;;; ENCODE-SORTS : module -> SortEncodingMap
;;;
(defun encode-sorts (module)
  (with-in-module (module)
    (let ((families (module-sort-families module))
	  (trs-sm nil))
      (do ((i 0 (1+ i))
	   (fm-list families (cdr fm-list)))
	  ((endp fm-list))
	(declare (type fixnum i))
	(do ((j 1 (* j 2))
	     (sorts (car fm-list) (cdr sorts)))
					; the first one is always the
					; family sort (error sort, kind ...)
	    ((endp sorts))
	  (declare (type fixnum j))
	  (push (make-sort-coding-map-entry
		 (car sorts)		; sort
		 i			; family-id
		 nil			; sort-code set later
		 j			; sort-id bit
		 )
		trs-sm)))
      ;; assign for each sort its sort-code
      ;; which is a logior sum of its own sort-id bit and that of lower sorts.
      (dolist (sem trs-sm)
	(setf (sort-coding-map-sort-code sem)
	      (reduce #'logior (cons (sort-coding-map-sort-id-bit sem)
				     (mapcar #'(lambda (x)
						 (sort-to-sort-id-bit x trs-sm))
					     (subsorts (sort-coding-map-sort sem)))
				     ))))
      ;;
      (nreverse trs-sm))))


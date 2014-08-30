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
				Module:trs-comp
			       File:indexing.lisp
=============================================================================|#

;;; GENERAL DISCRIMINATION TREE

;;; NLIST ::= (count . elements)
;;;
(defun make-empty-nlist ()
  (cons 0 nil))

;;; number of elements a nlist
(dfun nlist-number (x) (car x))

;;; elements in nlist
(defun nlist-list (x) (cdr x))

;;; addd a new element to an nlist
(defun nlist-push (item nlist)
  (incf (car nlist))
  (push item (cdr nlist))
  nlist)

;;; THE DESCRIMINATION TREE
;;; 
(defstruct (dtree (:type vector))
  (first nil)
  (next nil)
  (atoms nil)
  (var (make-empty-nlist)))


;;; *****************
;;; OPERATOR ENCODING
;;; *****************
;;; each operator in a module is encoded into natural numbers.
;;; op-encode-table
;;;   operator -> natural number
;;; op-info-array
;;;   natural number -> (operator . 
;;;

;;; Fetch (or make) operator encode table
;;;

(defun get-module-op-map-table (module)

;;; D-TREE for sort assignment
;;; ** Assumption **
;;; operator names are canonicalized, i.e., it is a simbole and
;;; is modified by its number of arguments and module-name.
;;;
(let ((operator-names nil))

  ;;; Fetch (or make) the dtree 
  (defun get-sort-assignment-dtree (operator)
    (let ((internal-name (operator-internal-name operator)))
    (cond ((get (operator-internal-name operator) ':sort-tree))
	  ))))


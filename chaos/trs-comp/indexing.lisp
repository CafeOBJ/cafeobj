;;;-*-Mode:LISP; Package: CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: indexing.lisp,v 1.1.1.1 2003-06-19 08:29:44 sawada Exp $
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


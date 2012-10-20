(in-package :chaos)

;;; file: clause.lisp

;;; SORT-LITERALS : Clause -> Clause'
;;;
(defun sort-literals (c)
  (declare (type clause c)
	   (values clause))
  (setf (clause-literals c)
    (sort (clause-literals c)
	  #'(lambda (x y)
	      (declare (type literal x y))
	      (not (eq (compare-literal x y) :less))
	      ;; (eq (compare-literal x y) :less)
	      )
	  ))
  c)
;;; EOF

;;; $Id:

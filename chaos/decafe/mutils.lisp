;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: mutils.lisp,v 1.1.1.1 2003-06-19 08:28:00 sawada Exp $
(in-package :chaos)
#|==============================================================================
				 System: CHAOS
				 Module: deCafe
			       File: mutils.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; === DESCRIPTION ============================================================
;;; Utilities specific to process module expressions.
;;;

;;; **********
;;; MISC UTILS__________________________________________________________________
;;; **********

;;; makes sequence of variables with canonical names (natural numbers).
;;;
(defun make-psuedo-vars (l)
  (do ((r l (cdr r))
       (i 0 (1+ i))
       (res nil (cons (make-variable-term (term-sort (car r)) i)
		      res)))
      ((null r) (nreverse res))
    (declare (type fixnum i))))

;;; makes sequence of variables with canonical names (natural numbers)
;;;
(defun make-psuedo-vars-from-sorts (l)
  (do ((r l (cdr r))
       (i 0 (1+ i))
       (res nil (cons (make-variable-term (car r) i) res)))
      ((null r) (nreverse res))
    (declare (type fixnum i)))
  )

(defun appropriate-method (srcmod module op)
  (when (or (null module)
	    (not (member op
			 (module-all-operators module)
			 :test #'(lambda (x y)
				   (operator= x (opinfo-operator y)))
			 )))
    (setq module (operator-module op)))
  (let ((arnum (operator-num-args op))
	;; (theory (operator-theory op)) ; not used now
	)
    (declare (type fixnum arnum))
    (let ((val (remove-if-not
		#'(lambda (opinfo)
		    (let ((opr (opinfo-operator opinfo)))
		      (and (= arnum (the fixnum (operator-num-args opr)))
                           ;; * todo * is-similar-theory
			   ;; (is-similar-theory (operator-theory opr) theory)
			   (eq srcmod (operator-module opr)))))
		(module-all-operators srcmod))))
      (if val
	  (if (null (cdr val))
	      (car val)
	      nil)
	  nil))))

(defun modexp-eval-principal-op (mod)
  (let ((all-ops (module-all-operators mod)))
    (dolist (op (reverse all-ops) (car all-ops))
      (when (eq mod (operator-module op)) (return op))
      )))

;;;
;;; MODMORPH-CHECK-RANK
;;;
(defun modmorph-check-rank (newmod oldmod map method)
  (let ((modmap (modmorph-module map))
	(sortmap (modmorph-sort map))
	(ar (method-arity method))
	(coar (method-coarity method)))
    (setf (method-arity method)
	  (modmorph-sorts-image-create newmod
				       oldmod
				       modmap
				       sortmap
				       ar))
    (setf (method-coarity method)
	  (modmorph-sort-image-create newmod
				      oldmod
				      modmap
				      sortmap
				      coar))
    ))


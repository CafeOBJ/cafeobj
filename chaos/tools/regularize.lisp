;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: regularize.lisp,v 1.1.1.1 2003-06-19 08:29:40 sawada Exp $
(in-package :chaos)
#|==============================================================================
				 System: Chaos
			         Module: tools
			     File: regularize.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; == DESCRIPTION =============================================================
;;; procedure for regularizing the signature of a module.
;;;


;;; REGULARIZE-SIGNATURE : Module -> Module'
;;; regularize a signature of given module.
;;;
(defun regularize-signature-internal (module)
  ;;
  (unless *regularize-signature*
    (return-from regularize-signature-internal nil))
  ;;
  (with-in-module (module)
    (let ((*print-indent* (+ *print-indent* 2)))
      ;; init.
      (setf (module-sorts-for-regularity module) nil
	    (module-methods-for-regularity module) nil
	    (module-void-methods module) nil)
      ;;
      (multiple-value-bind (empty-sorts
			    new-sorts
			    new-methods
			    redundant-methods
			    empty-methods)
	  (examine-regularity module)
	;; declare new sorts in module
	(dolist (new-sort new-sorts)
	  (unless (memq new-sort (module-sorts-for-regularity module))
	    (push new-sort (module-sorts-for-regularity module))
	    (add-sort-to-module new-sort module)
	    (declare-subsort-in-module
	     ` ((,new-sort :< ,@(and-sort-components new-sort)))
	       module)
	    (unless *chaos-quiet*
	      (let ((*standard-output* *error-output*))
		(print-next)
		(princ "-- declaring sort [")
		(print-sort-name new-sort module)
		(princ " <")
		(dolist (s (and-sort-components new-sort))
		  (princ " ")
		  (print-sort-name s module))
		(princ "], for regularity.")))
	    ))
	;; declare new operators.
	(dolist (m new-methods)
	  (let ((name (operator-symbol (car m)))
		(ranks (cdr m)))
	    (dolist (rank ranks)
	      (multiple-value-bind (op meth)
		  (declare-operator-in-module name
					      (car rank)
					      (cadr rank)
					      module)
		(declare (ignore op))
		(unless *chaos-quiet*
		  (let ((*standard-output* *error-output*))
		    (print-next)
		    (princ "-- declaring operator ")
		    (print-chaos-object meth)
		    (princ " for regularity.")))
		(pushnew meth (module-methods-for-regularity module))
		))))

	;; set void-methods -- not used now?
	(dolist (m empty-methods)
	  (pushnew m (module-void-methods module) :test #'eq))

	;; reports misc infos.
	(unless *chaos-quiet*
	  (when empty-sorts
	    (let ((*standard-output* *error-output*))
	      (print-next)
	      (format t ">> The following sorts are empty:")
	      (dolist (s empty-sorts)
		(print-next)
		(print-sort-name s module))))
	  (when redundant-methods
	    (let ((*standard-output* *error-output*))
	      (print-next)
	      (format t ">> The following operators are detected as redundant,")
	      (print-next)
	      (format t "   due to the above new operators.")
	      (dolist (m redundant-methods)
		(print-next)
		(reg-report-method m module))))
	  (when empty-methods
	    (let ((*standard-output* *error-output*))
	      (print-next)
	      (format t ">> The following operators have empty arity:")
	      (dolist (m empty-methods)
		(print-next)
		(reg-report-method m module))))
	  )
	;;
	t))))

;;;
;;; REGULARIZE-SIGNATURE
;;;
(defun regularize-signature (module)
  (let ((chaos-quiet *chaos-quiet*)
	;; (*chaos-verbose* t)
	(*regularize-signature* t)
	(*auto-reconstruct* t))
    (declare (special *regularize-signature*
		      *auto-reconstruct*
		      ;; *chaos-verbose*
		      *chaos-quiet*))
    (setq *chaos-quiet* nil)
    (regularize-signature-internal module)
    (mark-need-parsing-preparation module)
    (setq *chaos-quiet* t)
    (compile-module module)
    (setq *chaos-quiet* chaos-quiet)
    ))


;;; EOF

;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: eval-mod.lisp,v 1.3 2007-03-05 12:01:58 sawada Exp $
(in-package :chaos)
#|==============================================================================
				 System: CHAOS
				  Module: eval
			      File: eval-mod.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; ***************************
;;; TOP LEVEL MODEXPR EVALUATOR
;;; ***************************

;;; MODEXP-TOP-LEVEL-EVAL pre-modexp
;;; given a module expression no yet parsed, parses it, then
;;; evaluate the modexp.
;;;
(defun modexp-top-level-eval (modexp)
  (let ((meparse (parse-modexp modexp)))
    (if (equal "THE-LAST-MODULE" meparse)
	(if *last-module*
	    *last-module*
	    (with-output-chaos-error ('no-context)
	      (princ "no context (current) module")
	      ))
	(eval-modexp-top (normalize-modexp meparse)))
    ))

;;; EVAL-MOD
;;; similar to MODEXP-TOP-LEVEL-EVAL.
;;; specially handles the modexp "%" (opening module).
;;;
(defun eval-mod (toks &optional (change-context *auto-context-change*))
  (if (null toks)
      (if *last-module*
	  *last-module*
	  (with-output-chaos-error ('no-context)
	    (princ "no selected(current) module.")
	    ))
      (if (equal '("%") toks)
	  (if *open-module*
	      (let ((mod (find-module-in-env (normalize-modexp "%"))))
		(unless mod
		  (with-output-panic-message ()
		    (princ "could not find % module!!!!")
		    (chaos-error 'panic)))
		(when change-context
		  (change-context *last-module* mod))
		mod)
	      (with-output-chaos-warning ()
		(princ "no module is opening.")
		(chaos-error 'no-open-module)))
	  (let ((val (modexp-top-level-eval toks)))
	    (if (modexp-is-error val)
		(if (and (null (cdr toks))
			 (<= 4 (length (car toks)))
			 (equal "MOD" (subseq (car toks) 0 3)))
		    (let ((val (read-from-string (subseq (car toks) 3))))
		      (if (integerp val)
			  (let ((nmod (print-nth-mod val))) ;;; !!!
			    (when change-context
			      (change-context *last-module* nmod))
			    nmod)
			  (with-output-chaos-error ('no-such-module)
			    (format t "could not evaluate the modexp ~a" toks)
			    )))
		    (with-output-chaos-error ('no-such-module)
		      (format t "undefined module? ~a" toks)
		      ))
		(progn
		  (when change-context
		    (change-context *last-module* val))
		  val))))))

;;; what to do with this one?

(defun print-nth-mod (&rest ignore)
  (declare (ignore ignore))
  nil)

;;; EVAL-MOD-EXT
;;; evaluate modexp not yet parsed with some extension:
;;; - handles "sub"     --- submodule
;;;           "param"   --- parameter
;;;   
(defun eval-mod-ext (toks &optional
			  (change-context *auto-context-change* force?))
  (when (equal toks ".")
    (setq toks nil))
  (when (and (listp toks)
	     (equal (car (last toks)) "."))
    (setq toks (butlast toks)))
  (let ((it (car toks)))
    (when (equal it ".")
      (setq it nil)
      (setq toks nil))
    (cond ((and (equal "sub" it)
		(cadr toks)
		(parse-integer (cadr toks) :junk-allowed t))
	   (let* ((no (read-from-string (cadr toks)))
		  (mod (eval-mod-ext (cddr toks) nil))
		  (sub (nth-sub (1- no) mod)))
	     (if sub
		 (when change-context
		   (change-context *last-module* sub))
		 (progn (princ "** Waring : No such sub-module") (terpri) nil))))
	  ((and (equal "param" it)
		(cadr toks)
		(parse-integer (cadr toks) :junk-allowed t))
	   (let* ((no (read-from-string (cadr toks)))
		  (mod (eval-mod-ext (cddr toks) nil))
		  (params (module-parameters mod))
		  (param (nth (1- no) params)))
	     (if param
		 (when change-context
		   (change-context *last-module* (cdr param)))
		 (with-output-chaos-error ('no-such-parameter)
		   (princ "No such parameter")
		   ))))
	  ((and (null toks) change-context force?)
	   (when *last-module*
	     (change-context *last-module* nil)))
	  (t (eval-mod toks change-context))
	  )))

;;; EOF

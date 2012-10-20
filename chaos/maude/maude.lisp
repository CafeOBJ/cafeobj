;;;-*-Mode:LISP; Package: CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: maude.lisp,v 1.1.1.1 2003-06-19 08:28:19 sawada Exp $
(in-package :chaos)
#|=============================================================================
			     System:CHAOS
			     Module:maude
			    File:maude.lisp
=============================================================================|#

;;; **********
;;; IDENTIFIER
;;; **********

;;; FMOD-TRANS-IDENT
;;;
(defparameter fmod-id-trans-table
  '((#\. #\@)
    (#\_ #\-)
    (#\` #\')
    (#\( #\|)
    (#\) #\|)
    (#\[ #\|)
    (#\] #\|)
    (#\{ #\|)
    (#\} #\|)))

(defun fmod-trans-ident (ident)
  (intern (parallel-substitute fmod-id-trans-table (string ident))))

(defmacro fmod-sort-name-map (module)
  `(getf (module-infos ,module) ':fmod-sort-name-map))

(defmacro fmod-module-name-map (module)
  `(getf (module-infos ,module) ':fmod-module-name-map))

(defmacro fmod-op-name-map (module)
  `(getf (module-infos ,module) ':fmod-op-name-map))

(defmacro fmod-var-name-map (module)
  `(getf (module-infos ,module) ':fmod-var-name-map))

(defun fmod-get-module-name (module name)
  (or (cdr (assoc name (fmod-module-name-map module)
		  :test #'equal))
      (let ((tname (fmod-trans-ident name)))
	(push (cons name tname)
	      (fmod-module-name-map module))
	tname)))
	      
(defun fmod-get-sort-name (module sort-name)
  (or (cdr (assq sort-name (fmod-sort-name-map module)))
      (let ((tname (fmod-trans-ident sort-name)))
	(push (cons sort-name tname)
	      (fmod-sort-name-map module))
	tname)))

(defun fmod-get-op-name (module op-name)
  (or (cdr (assq op-name (fmod-op-name-map module)))
      (let ((tname (fmod-trans-ident op-name)))
	(push (cons op-name tname)
	      (fmod-op-name-map module))
	tname)))

(defun fmod-get-var-name (module var-name)
  (or (cdr (assq var-name (fmod-var-name-map module)))
      (let ((tname (fmod-trans-ident var-name)))
	(push (cons var-name tname)
	      (fmod-var-name-map module))
	tname)))

;;; ****
;;; TERM
;;; ****
(defun trs-to-fmod-term (trs-term trs)
  (with-output-to-string (str)
    (let ((*standard-output* str))
      (print-trs-term-as-fmod-term trs-term trs)
      str)))

(defun print-trs-term-as-fmod-term (trs-term trs)
  (let ((mod (trs$module trs)))
    (case (trs-term-type trs-term)
      (:var (princ (fmod-get-var-name mod (trs-term-head trs-term))))
      (:op (let ((op-name (fmod-get-op-name mod
					    (trs-term-head trs-term)))
		 (prv nil))
	     (princ op-name)
	     (when (trs-term-subterms trs-term)
	       (princ "(")
	       (do ((subs (trs-term-subterms trs-term) (cdr subs)))
		   ((null subs))
		 (print-trs-term-as-fmod-term (car subs trs))
		 (when prv (princ ", "))
		 (setq prv t)
		 )
	       (princ ")"))))
      (:builtin-value nil)
      (:lisp nil)
      (:glisp nil)
      )))
      

;;; *******************
;;; OPERATOR ATTRIBUTES
;;; *******************


;;; SHOW-FMOD module : -> void
;;;
(defun show-fmod (&optional modexp)
  (let ((*print-circle* nil)
	(*print-case* :downcase)
	(*print-escape* nil))
    (let ((modval (trs-get-mod-or-error modexp)))
      (show-fmod* modval))
    ))

;;;
;;; SHOW-FMOD*
;;;
(defun show-fmod* (&optional (module (or *last-module*
					 *current-module*)))
  (let ((trs (get-module-trs module)))
    ;;
    (princ "fmod ")
    (print-mod-name module *standard-output* nil t)
    (princ " is ")
    (let ((*print-indent* (+ 2 *print-indent*)))
      (print-next)
      ;; sorts
      (princ "sorts")
      (let ((*print-indent* (+ 5 *print-indent*)))
	(dolist (sinfo (trs$sort-name-map trs))
	  (unless (err-sort-p (car sinfo))
	    (let ((name (format nil " ~a"
				(fmod-get-sort-name module (cdr sinfo)))))
	      (print-check 0 (length name))
	      (princ name)
	      )))
	(princ " ."))
      (print-next)
      ;; subsort relations
      (when (trs$sort-graph trs)
	(dolist (sg (trs$sort-graph trs))
	  (format t "subsorts ~a < ~a ."
		  (fmod-get-sort-name module (car sg))
		  (fmod-get-sort-name module (cadr sg)))
	  (print-next)))
      ;; operator declarations
      (dolist (opinfo (trs$op-info-map trs))
	(let* ((meth (car opinfo))
	       (info (cdr opinfo))
	       (op-name (fmod-get-op-name module (first info)))
	       (arity (mapcar #'(lambda (x)
				(fmod-get-sort-name module x))
			      (second info)))
	       (coarity (fmod-get-sort-name module (third info))))
	  (if (method-constructor meth)
	      (format t "cop ~a : ~{~a~^ ~} -> ~a "
		      op-name
		      arity
		      coarity)
	      (format t "op ~a : ~{~a~^ ~} -> ~a "
		      op-name
		      arity
		      coarity))
	  ;; attribute
	  ;;
	  (princ " .")
	  (print-next)
	  ))
    )))

;;; EOF

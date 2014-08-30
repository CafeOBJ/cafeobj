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
				 System: Chaos
			       Module: construct
			      File: variable.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; ********************
;;; VARIABLE DECLARATION _______________________________________________________
;;; ********************
(defun check-var-name-overloading-with-builtin (var-name sort module)
  (let ((sorts (module-all-sorts module)))
    (dolist (bi sorts)
      (when (and (sort-is-builtin bi) (not (sort= *id-sort* bi)))
	(let ((token-pred (bsort-token-predicate bi)))
	  (when (and token-pred
		     (funcall token-pred var-name)
		     (is-in-same-connected-component* sort
						      bi
						      (module-sort-order module)))
	    (return-from check-var-name-overloading-with-builtin bi)
	    ))))
    nil))

(defun declare-variable-in-module (var-name sort-ref
					    &optional (module *current-module*))

  #||
  (when (and (consp var-name)
	     (eq (car var-name) '|String|))
    ;; (setq var-name (format nil "\"~s\"" (cadr var-name)))
    (setq var-name (cadr var-name))
    )
  ||#
  (let ((mod (if (module-p module)
		 module
		 (find-module-in-env module))))
    (unless mod
      (with-output-panic-message ()
	(princ "internal error, no such module ")
	(print-mod-name module)
	(princ ", variable declaration for ")
	(princ var-name)
	(princ " failed.")
	(chaos-error 'no-such-module)))

    (let ((sort (if (sort-struct-p sort-ref) sort-ref
		    (find-sort-in mod sort-ref))))
      (unless sort
	(with-output-chaos-error ('no-such-sort)
	  (princ "could not find sort ")
	  (princ sort-ref)
	  (princ ", variable declaration for ")
	  (princ var-name)
	  (princ " is ignored.")
	  ))
      ;; check name ---
      (cond ((stringp var-name)
	     ;; name conflict check with builtin constants
	     (let ((bi (check-var-name-overloading-with-builtin var-name sort module)))
	       (when bi
		 (with-output-chaos-warning ()
		   (format t "variable name ~s is conflicting with built-in constant of sort " var-name)
		   (print-sort-name bi module)
		   (print-next)
		   (princ "... ignored."))
		 (return-from declare-variable-in-module nil)))
	     #||
	     (let ((ops nil))
	       ;; name conflict check with existing op
	       (setq ops (find-all-qual-operators-in module var-name 0))
	       (when ops
		 (with-output-chaos-warning ()
		   (format t "declaring variable ~s:" var-name)
		   (print-next)
		   (format t "  there already is an constant operator with the same name.")
		   (print-next)
		   (princ "... ignoring")
		   (return-from declare-variable-in-module nil)
		   ))
	       )
	     ||#
	     ;; check name --
	     (when (eql #\` (char var-name 0))
	       (with-output-chaos-error ('invalid-var-decl)
		 (format t "variable name must not start with \"`\",")
		 (print-next)
		 (princ "'`' is reserved for the prefix of pseudo variables declared on the fly.")
		 ))
	     ;; name must be begin with
	     (setf var-name (intern var-name)))
	    (t (unless (symbolp var-name)
		 (with-output-chaos-error ('invalid-variable-name)
		   (princ "invalid variable name ")
		   (princ var-name)
		   (chaos-error 'invalid-var-decl))))
	    )
      ;; 
      (let ((old (assoc var-name (module-variables mod)))
	    var)
	#||
	(when (and old (sort= sort (variable-sort (cdr old))))
	  (return-from declare-variable-in-module (cdr old)))
	||#
	(when old
	  (with-output-chaos-warning ()
	    (princ "variable ")
	    (princ (string var-name))
	    (princ " is already declared as sort ")
	    (princ (string (sort-id (variable-sort (cdr old)))))
	    #||
	    (princ ", but redefined as sort ")
	    (princ (string (sort-id sort)))
	    ||#
	    (princ ", ignored.")
	    (return-from declare-variable-in-module nil)
	    ))
	(setf var (make-variable-term sort var-name))
	(push (cons var-name var) (module-variables mod))
	;;
	(symbol-table-add (module-symbol-table mod)
			  var-name
			  var)
	;;
	var))))
 
(defun declare-pvariable-in-module (var-name sort-ref
				    &optional (module *current-module*))
  (let ((mod (if (module-p module)
		 module
	       (find-module-in-env module))))
    (unless mod
      (with-output-panic-message ()
	(princ "internal error, no such module ")
	(print-mod-name module)
	(princ ", pseud constant declaration for ")
	(princ var-name)
	(princ " failed.")
	(chaos-error 'no-such-module)))

    (let ((sort (if (sort-struct-p sort-ref) sort-ref
		    (find-sort-in mod sort-ref))))
      (unless sort
	(with-output-chaos-error ('no-such-sort)
	  (princ "could not find sort ")
	  (princ sort-ref)
	  (princ ", pseud constant declaration for ")
	  (princ var-name)
	  (princ " is ignored.")
	  ))

      #||
      ;; check name --
      (when (eql #\` (char (the simple-string (string var-name)) 0))
	(with-output-chaos-error ('invalid-var-decl)
	  (format t "variable name must not start with \"`\",")
	  (print-next)
	  (princ "this is reserved for pseud variables declared on the fly.")
	  ))
      ||#
      ;;
      (if (stringp var-name)
	  (setf var-name (intern var-name))
	  (unless (symbolp var-name)
	    (with-output-panic-message ()
	      (princ "internal error: invalid pconstant name ")
	      (princ var-name)
	      (chaos-error 'invalid-var-decl))))
      
      (let ((old (assoc var-name (module-variables mod)))
	    var)
	(when (and old (sort= sort (variable-sort (cdr old))))
	  (return-from declare-pvariable-in-module (cdr old)))
	(when old
	  (with-output-chaos-warning ()
	    (princ "pseud constant ")
	    (princ (string var-name))
	    (princ " once declared as sort ")
	    (princ (string (sort-id (variable-sort (cdr old)))))
	    (princ ", but re-declared as sort ")
	    (princ (string (sort-id sort)))
	    (princ ", ignored.")
	    (return-from declare-pvariable-in-module nil)
	    ))
	(setf var (make-pvariable-term sort var-name))
	(push (cons var-name var) (module-variables mod))
	;;
	(symbol-table-add (module-symbol-table mod)
			  var-name
			  var)
	;;
	var))))

;;;
;;; DECLARE-ERROR-VARIABLES-IN
;;;
(defun declare-error-variables-in (module)
  (with-in-module (module)
    (dolist (var-decl (module-error-var-decl module))
      (declare-variable var-decl))))

;;; EOF

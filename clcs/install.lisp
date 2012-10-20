;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: "CONDITIONS"; Base: 10 -*-

(in-package "CONDITIONS")

(defvar *shadowed-symbols* 
  '(BREAK ERROR CERROR WARN CHECK-TYPE ASSERT ETYPECASE CTYPECASE ECASE CCASE))

(defun install-symbol (real clcs)
  (unless (get real ':definition-before-clcs)
    (setf (get real ':definition-before-clcs)
	  (symbol-function real)))
  (unless (eq (symbol-function real)
	      (symbol-function clcs))	       
    (setf (symbol-function real)
	  (symbol-function clcs))))

(defun revert-symbol (real)
  (when (and (get real ':definition-before-clcs)
	     (not (eq (symbol-function real)
		      (get real ':definition-before-clcs))))
    (setf (symbol-function real)
	  (get real ':definition-before-clcs))))

(defvar *clcs-redefinitions*
  (nconc (mapcar #'(lambda (symbol)
		     (list (intern (symbol-name symbol) "LISP") symbol))
		 *shadowed-symbols*)
	 '((compile-file clcs-compile-file)
	   (compile clcs-compile)
           (load clcs-load)
           (open clcs-open)
	   #+kcl (si::break-level si::clcs-break-level)
	   #+kcl (si::terminal-interrupt si::clcs-terminal-interrupt)
	   #+kcl (si::break-quit si::clcs-break-quit)
	   #+kcl (si::error-set clcs-error-set)
	   #+kcl (si::universal-error-handler clcs-universal-error-handler))))

(defun install-clcs-symbols ()
  (dolist (r *clcs-redefinitions*)
    (install-symbol (first r) (second r)))
  nil)

(defun revert-clcs-symbols ()
  (dolist (r (reverse *clcs-redefinitions*))
    (revert-symbol (first r)))
  nil)

(defun clcs-compile-file (file &rest args)
  (loop (with-simple-restart (retry "Retry compiling file ~S." file)
	  (let ((values (multiple-value-list 
			    (apply (or (get 'compile-file ':definition-before-clcs)
				       #'compile-file)
				   file args))))
	    (unless #+kcl compiler::*error-p* #-kcl nil
	      (return-from clcs-compile-file
		(values-list values)))
	    (error "~S failed." 'compile-file)))))

(defun clcs-compile (&rest args)
  (loop (with-simple-restart (retry "Retry compiling ~S." (car args))
	  (let ((values (multiple-value-list 
			    (apply (or (get 'compile ':definition-before-clcs)
				       #'compile-file)
				   args))))
	    (unless #+kcl compiler::*error-p* #-kcl nil
	      (return-from clcs-compile
		(values-list values)))
	    (error "~S failed." 'compile)))))

(defun clcs-load (file &rest args)
  (loop (with-simple-restart (retry "Retry loading file ~S." file)
          (return-from clcs-load 
                       (apply (or (get 'load ':definition-before-clcs) #'load)
                              file args)))))

(defun clcs-open (file &rest args)
  (loop (with-simple-restart (retry "Retry opening file ~S." file)
          (return-from clcs-open
                       (apply (or (get 'open ':definition-before-clcs) #'open)
                              file args)))))

#+(or kcl lucid cmu)
(install-clcs-symbols)

#+dsys
(defun dsys::retry-operation (function retry-string)
  (loop (with-simple-restart (retry retry-string)
	  (return-from dsys::retry-operation
	    (funcall function)))))

#+dsys
(defun dsys::operate-on-module (module initial-state system-operation)
  (if (null dsys::*retry-operation-list*)
      (dsys::operate-on-module1 module initial-state system-operation)
      (let ((retry-operation (car (last dsys::*retry-operation-list*)))
	    (dsys::*retry-operation-list* (butlast dsys::*retry-operation-list*)))
	(restart-bind ((retry 
			#'(lambda (&rest ignore)
			    (declare (ignore ignore))
			    (funcall (car retry-operation)))
			:report-function
			#'(lambda (stream)
			    (write-string (cdr retry-operation) stream))))
	   (dsys::operate-on-module module initial-state system-operation)))))

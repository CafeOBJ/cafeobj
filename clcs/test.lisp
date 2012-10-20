;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: "CONDITIONS"; Base: 10 -*-

(in-package "CONDITIONS")

(defvar *internal-error-table* (make-hash-table :test 'equal))

(defmacro find-internal-error-data (error-name error-format-string)
  `(gethash (list ,error-name ,error-format-string) *internal-error-table*))

(defun clcs-universal-error-handler (error-name correctable function-name
			             continue-format-string error-format-string
			             &rest args)
  (if correctable
      (with-simple-restart 
	  (continue "~a" (apply #'format nil continue-format-string args))
	(error 'internal-simple-error 
	       :function-name function-name
	       :format-string error-format-string 
	       :format-arguments args))
      (let ((e-d (find-internal-error-data error-name error-format-string)))
	(print e-d)
	(if e-d
	    (let ((condition-name (car e-d)))
	      (apply #'error condition-name
		     :function-name function-name
		     (let ((k-a (mapcan #'list (cdr e-d) args)))
		       (if (simple-condition-class-p condition-name)
			   (list* :format-string error-format-string
				  :format-arguments args
				  k-a)
			   k-a))))
	    (error 'internal-simple-error :function-name function-name
		   :format-string error-format-string :format-arguments args)))))

(defun set-internal-error (error-keyword error-format condition-name
					 &rest keyword-list)
  (setf (find-internal-error-data error-keyword error-format)
	(cons condition-name keyword-list)))

(defun initialize-internal-error-table ()
  (declare (special *internal-error-list*))
  (clrhash *internal-error-table*)
  (dolist (error-data *internal-error-list*)
    (apply #'set-internal-error (cdr error-data))))

(defparameter *internal-error-list*
  '(("FEwrong_type_argument" :wrong-type-argument "~S is not of type ~S."
     internal-type-error :datum :expected-type)
    ("FEtoo_few_arguments" :too-few-arguments "~S [or a callee] requires more than ~R argument~:p." 
     internal-simple-control-error) ; |<function>| |top - base|
    ("FEtoo_few_argumentsF" :too-few-arguments "Too few arguments."
     internal-simple-control-error) ; |<function>| |args|
    ("FEtoo_many_arguments" :too-many-arguments "~S [or a callee] requires less than ~R argument~:p."
     internal-simple-control-error) ; |<function>| |top - base|
    ("FEtoo_many_argumentsF" :too-many-arguments "Too many arguments."
     internal-simple-control-error) ; |<function>| |args|
    ("FEinvalid_macro_call" :invalid-form "Invalid macro call to ~S."
     internal-simple-program-error) ; |<function>|
    ("FEunexpected_keyword" :unexpected-keyword "~S does not allow the keyword ~S."
     internal-simple-control-error) ; |<function>| |key|
    ("FEunbound_variable" :unbound-variable "The variable ~S is unbound."
     internal-unbound-variable :name) ; |sym|
    ("FEundefined_function" :undefined-function "The function ~S is undefined."
     internal-undefined-function :name)
    ("FEinvalid_function" :invalid-function "~S is invalid as a function."
     internal-simple-program-error) ; |obj|
    ("check_arg_failed" :too-few-arguments "~S [or a callee] requires ~R argument~:p,~%\
but only ~R ~:*~[were~;was~:;were~] supplied."
     internal-simple-control-error) ; |<function>| |n| |top - base|
    ("check_arg_failed" :too-many-arguments "~S [or a callee] requires only ~R argument~:p,~%\
but ~R ~:*~[were~;was~:;were~] supplied."
     internal-simple-control-error) ; |<function>| |n| |top - base|
    ("ck_larg_at_least" :error "APPLY sended too few arguments to LAMBDA."
     internal-simple-control-error) 
    ("ck_larg_exactly" :error "APPLY sended too few arguments to LAMBDA."
     internal-simple-control-error) 
    ("keyword_value_mismatch" :error "Keywords and values do not match."
     internal-simple-error) ;??
    ("not_a_keyword" :error "~S is not a keyword."
     internal-simple-error) ;??
    ("illegal_declare" :invalid-form "~S is an illegal declaration form."
     internal-simple-program-error)
    ("not_a_symbol" :invalid-variable "~S is not a symbol."
     internal-simple-error) ;??
    ("not_a_variable" :invalid-variable "~S is not a variable."
     internal-simple-program-error)
    ("illegal_index" :error "~S is an illegal index to ~S."
     internal-simple-error)
    ("vfun_wrong_number_of_args" :error "Expected ~S args but received ~S args"
     internal-simple-control-error)
    
    ("end_of_stream" :error "Unexpected end of ~S."
     internal-end-of-file :stream)
    ("open_stream" :error "~S is an illegal IF-DOES-NOT-EXIST option."
     internal-simple-control-error)
    ("open_stream" :error "The file ~A already exists."
     internal-simple-file-error :pathname)
    ("open_stream" :error "Cannot append to the file ~A."
     internal-simple-file-error :pathname)
    ("open_stream" :error "~S is an illegal IF-EXISTS option."
     internal-simple-control-error)
    ("close_stream" :error "Cannot close the standard output."
     internal-simple-stream-error) ; no stream here!!
    ("close_stream" :error "Cannot close the standard input."
     internal-simple-stream-error) ; no stream here!!
    ("too_long_file_name" :error "~S is a too long file name."
     internal-simple-file-error :pathname)
    ("cannot_open" :error "Cannot open the file ~A."
     internal-simple-file-error :pathname)
    ("cannot_create" :error "Cannot create the file ~A."
     internal-simple-file-error :pathname)
    ("cannot_read" :error "Cannot read the stream ~S."
     internal-simple-stream-error :stream)
    ("cannot_write" :error "Cannot write to the stream ~S."
     internal-simple-stream-error :stream)
    ))

(initialize-internal-error-table)

(defun condition-backtrace (condition)
  (let* ((*debug-io* *error-output*)
	 (si::*ihs-base* (1+ si::*ihs-top*))
         (si::*ihs-top* (1- (si::ihs-top)))
         (si::*current-ihs* si::*ihs-top*)
         (si::*frs-base* (or (si::sch-frs-base si::*frs-top* si::*ihs-base*)
			     (1+ (si::frs-top))))
         (si::*frs-top* (si::frs-top))
         (si::*break-env* nil))
    (format *error-output* "~%~A~%" condition)
    (si::simple-backtrace)))

(defvar *error-set-break-p* nil)

(defun clcs-error-set (form)
  (let ((cond nil))
    (restart-case (handler-bind ((error #'(lambda (condition)
					    (unless (or si::*break-enable*
							*error-set-break-p*)
					      (condition-backtrace condition)
					      (return-from clcs-error-set condition))
					    (setq cond condition)
					    nil)))
		     (values-list (cons nil (multiple-value-list (eval form)))))
       (si::error-set ()
	  :report (lambda (stream)
		    (format stream "~S" `(si::error-set ',form)))
	  cond))))

(eval-when (compile load eval)

(defun reset-function (symbol) ; invoke compiler::compiler-clear-compiler-properties
  (setf (symbol-function symbol) (symbol-function symbol)))

(reset-function 'si::error-set)
(reset-function 'load)
(reset-function 'open)
)

(setq compiler::*compiler-break-enable* t)

(defun compiler::cmp-toplevel-eval (form)
   (let* (;;(si::*ihs-base* si::*ihs-top*) ; show the whole stack
          (si::*ihs-top* (1- (si::ihs-top)))
          (*break-enable* compiler::*compiler-break-enable*)
          (si::*break-hidden-packages*
           (cons (find-package 'compiler)
                 si::*break-hidden-packages*)))
         (si:error-set form)))

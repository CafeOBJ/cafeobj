;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: "CONDITIONS"; Base: 10 -*-

(IN-PACKAGE "CONDITIONS")

(eval-when (compile load eval)
(pushnew #+(or clos pcl) :clos-conditions #-(or clos pcl) :defstruct-conditions
	 *features*)
)

(eval-when (compile load eval)
(when (and (member :clos-conditions *features*)
	   (member :defstruct-conditions *features*))
  (dolist (sym '(simple-condition-format-string simple-condition-format-arguments
		 type-error-datum type-error-expected-type
		 case-failure-name case-failure-possibilities
		 stream-error-stream file-error-pathname package-error-package
		 cell-error-name arithmetic-error-operation
		 internal-error-function-name))
    (when (fboundp sym) (fmakunbound sym)))
  (setq *features* (remove :defstruct-conditions *features*)))
)

;;; Start

(DEFINE-CONDITION WARNING (CONDITION)
  ())

(DEFINE-CONDITION SERIOUS-CONDITION (CONDITION)
  ())

(DEFINE-CONDITION lisp:ERROR (SERIOUS-CONDITION)
  ())

(DEFUN SIMPLE-CONDITION-PRINTER (CONDITION STREAM)
  (APPLY #'FORMAT STREAM (SIMPLE-CONDITION-FORMAT-STRING    CONDITION)
	 		 (SIMPLE-CONDITION-FORMAT-ARGUMENTS CONDITION)))

(DEFINE-CONDITION SIMPLE-CONDITION (CONDITION)
  #-(or clos pcl)
  (FORMAT-STRING (FORMAT-ARGUMENTS '()))
  #+(or clos pcl)
  ((FORMAT-STRING :type string
		  :initarg :FORMAT-STRING
		  :reader SIMPLE-CONDITION-FORMAT-STRING)
   (FORMAT-ARGUMENTS :initarg :FORMAT-ARGUMENTS
		     :reader SIMPLE-CONDITION-FORMAT-ARGUMENTS
		     :initform '()))
  #-(or clos pcl)(:CONC-NAME %%SIMPLE-CONDITION-)
  (:REPORT SIMPLE-CONDITION-PRINTER))

(DEFINE-CONDITION SIMPLE-WARNING (#+(or clos pcl) SIMPLE-CONDITION WARNING)
  #-(or clos pcl)
  (FORMAT-STRING (FORMAT-ARGUMENTS '()))
  #+(or clos pcl)
  ()
  #-(or clos pcl)(:CONC-NAME %%SIMPLE-WARNING-)
  #-(or clos pcl)(:REPORT SIMPLE-CONDITION-PRINTER))

(DEFINE-CONDITION SIMPLE-ERROR (#+(or clos pcl) SIMPLE-CONDITION lisp:ERROR)
  #-(or clos pcl)
  (FORMAT-STRING (FORMAT-ARGUMENTS '()))
  #+(or clos pcl)
  ()
  #-(or clos pcl)(:CONC-NAME %%SIMPLE-ERROR-)
  #-(or clos pcl)(:REPORT SIMPLE-CONDITION-PRINTER))

(DEFINE-CONDITION STORAGE-CONDITION (SERIOUS-CONDITION) ())

(DEFINE-CONDITION STACK-OVERFLOW    (STORAGE-CONDITION) ())

(DEFINE-CONDITION STORAGE-EXHAUSTED (STORAGE-CONDITION) ())

(DEFINE-CONDITION TYPE-ERROR (lisp:ERROR)
  #-(or clos pcl)
  (DATUM EXPECTED-TYPE)
  #+(or clos pcl)
  ((DATUM :initarg :DATUM
	  :reader TYPE-ERROR-DATUM)
   (EXPECTED-TYPE :initarg :EXPECTED-TYPE
		  :reader TYPE-ERROR-EXPECTED-TYPE))
  (:report
    (lambda (condition stream)
      (format stream "~S is not of type ~S."
	      (TYPE-ERROR-DATUM CONDITION)
	      (TYPE-ERROR-EXPECTED-TYPE CONDITION)))))

(DEFINE-CONDITION SIMPLE-TYPE-ERROR (#+(or clos pcl) SIMPLE-CONDITION TYPE-ERROR)
  #-(or clos pcl)
  (FORMAT-STRING (FORMAT-ARGUMENTS '()))
  #+(or clos pcl)
  ()
  #-(or clos pcl)(:CONC-NAME %%SIMPLE-TYPE-ERROR-)
  #-(or clos pcl)(:REPORT SIMPLE-CONDITION-PRINTER))

(DEFINE-CONDITION CASE-FAILURE (TYPE-ERROR)
 #-(or clos pcl)
 (NAME POSSIBILITIES)
 #+(or clos pcl)
 ((NAME :initarg :NAME
	:reader CASE-FAILURE-NAME)
  (POSSIBILITIES :initarg :POSSIBILITIES
		 :reader CASE-FAILURE-POSSIBILITIES))
  (:REPORT
    (LAMBDA (CONDITION STREAM)
      (FORMAT STREAM "~S fell through ~S expression.~%Wanted one of ~:S."
	      (TYPE-ERROR-DATUM CONDITION)
	      (CASE-FAILURE-NAME CONDITION)
	      (CASE-FAILURE-POSSIBILITIES CONDITION)))))

(DEFINE-CONDITION PROGRAM-ERROR (lisp:ERROR)
  ())

(DEFINE-CONDITION CONTROL-ERROR (lisp:ERROR)
  ())

(DEFINE-CONDITION STREAM-ERROR (lisp:ERROR)
  #-(or clos pcl)
  (STREAM)
  #+(or clos pcl)
  ((STREAM :initarg :STREAM
	   :reader STREAM-ERROR-STREAM)))

(DEFINE-CONDITION END-OF-FILE (STREAM-ERROR)
  ()
  (:REPORT (LAMBDA (CONDITION STREAM)
	     (FORMAT STREAM "Unexpected end of file on ~S."
		     (STREAM-ERROR-STREAM CONDITION)))))

(DEFINE-CONDITION FILE-ERROR (lisp:ERROR)
  #-(or clos pcl)
  (PATHNAME)
  #+(or clos pcl)
  ((PATHNAME :initarg :PATHNAME
	     :reader FILE-ERROR-PATHNAME)))

(DEFINE-CONDITION PACKAGE-ERROR (lisp:ERROR)
  #-(or clos pcl)
  (PACKAGE)
  #+(or clos pcl)
  ((PACKAGE :initarg :PACKAGE
	    :reader PACKAGE-ERROR-PACKAGE)))

(DEFINE-CONDITION CELL-ERROR (lisp:ERROR)
  #-(or clos pcl)
  (NAME)
  #+(or clos pcl)
  ((NAME :initarg :NAME
	 :reader CELL-ERROR-NAME)))

(DEFINE-CONDITION UNDEFINED-FUNCTION (CELL-ERROR)
  ()
  (:REPORT (LAMBDA (CONDITION STREAM)
	     (FORMAT STREAM "The function ~S is undefined."
		     (CELL-ERROR-NAME CONDITION)))))

(DEFINE-CONDITION ARITHMETIC-ERROR (lisp:ERROR)
  #-(or clos pcl)
  (OPERATION OPERANDS)
  #+(or clos pcl)
  ((OPERATION :initarg :OPERATION
	      :reader ARITHMETIC-ERROR-OPERATION)))

(DEFINE-CONDITION DIVISION-BY-ZERO         (ARITHMETIC-ERROR)
  ())

(DEFINE-CONDITION FLOATING-POINT-OVERFLOW  (ARITHMETIC-ERROR)
  ())

(DEFINE-CONDITION FLOATING-POINT-UNDERFLOW (ARITHMETIC-ERROR)
  ())

(DEFINE-CONDITION ABORT-FAILURE (CONTROL-ERROR) ()
  (:REPORT "Abort failed."))


#+kcl
(progn

;;; When this form is present, the compiled behavior disagrees with
;;; the interpreted behavior.  The interpreted behavior is correct.
(define-condition internal-error (lisp:error)
  #-(or clos pcl)
  ((function-name nil))
  #+(or clos pcl)
  ((function-name :initarg :function-name
		  :reader internal-error-function-name
		  :initform 'nil))
  (:report (lambda (condition stream)
	     (when (internal-error-function-name condition)
	       (format stream "Error in ~S [or a callee]: "
		       (internal-error-function-name condition)))
	     #+(or clos pcl)(call-next-method))))

(defun internal-simple-error-printer (condition stream)
  (when (internal-error-function-name condition)
    (format stream "Error in ~S [or a callee]: "
	    (internal-error-function-name condition)))
  (apply #'format stream (simple-condition-format-string    condition)
	 		 (simple-condition-format-arguments condition)))

(define-condition internal-simple-error 
    (internal-error #+(or clos pcl) simple-condition)
  #-(or clos pcl)
  ((function-name nil) format-string (format-arguments '()))
  #+(or clos pcl)
  ()
  #-(or clos pcl)(:conc-name %%internal-simple-error-)
  (:report internal-simple-error-printer))

(define-condition internal-type-error 
    (#+(or clos pcl) internal-error type-error)
  #-(or clos pcl)
  ((function-name nil))
  #+(or clos pcl)
  ()
  #-(or clos pcl)(:conc-name %%internal-type-error-)
  #-(or clos pcl)(:report (lambda (condition stream)
			    (when (internal-error-function-name condition)
			      (format stream "Error in ~S [or a callee]: "
				      (internal-error-function-name condition)))
			    (format stream "~S is not of type ~S."
				    (type-error-datum condition)
				    (type-error-expected-type condition)))))

(define-condition internal-simple-program-error 
    (#+(or clos pcl) internal-simple-error program-error)
  #-(or clos pcl)
  ((function-name nil) format-string (format-arguments '()))
  #+(or clos pcl)
  ()
  #-(or clos pcl)(:conc-name %%internal-simple-program-error-)
  #-(or clos pcl)(:report internal-simple-error-printer))

(define-condition internal-simple-control-error 
    (#+(or clos pcl) internal-simple-error control-error)
  #-(or clos pcl)
  ((function-name nil) format-string (format-arguments '()))
  #+(or clos pcl)
  ()
  #-(or clos pcl)(:conc-name %%internal-simple-control-error-)
  #-(or clos pcl)(:report internal-simple-error-printer))


(define-condition internal-unbound-variable 
    (#+(or clos pcl) internal-error unbound-variable)
  #-(or clos pcl)
  ((function-name nil))
  #+(or clos pcl)
  ()
  #-(or clos pcl)(:conc-name %%internal-unbound-variable-)
  #-(or clos pcl)(:REPORT (LAMBDA (CONDITION STREAM)
			    (when (internal-error-function-name condition)
			      (format stream "Error in ~S [or a callee]: "
				      (internal-error-function-name condition)))
			    (FORMAT STREAM "The variable ~S is unbound."
				    (CELL-ERROR-NAME CONDITION)))))

#-(or pcl clos)
(defun internal-error-function-name (condition) 
  (etypecase condition
    (internal-error                
     (%%internal-error-function-name condition))
    (internal-simple-error         
     (%%internal-simple-error-function-name condition))
    (internal-type-error 
     (%%internal-type-error-function-name condition))
    (internal-simple-program-error
     (%%internal-simple-program-error-function-name condition))
    (internal-simple-control-error
     (%%internal-simple-control-error-function-name condition))
    (internal-unbound-variable  
     (%%internal-unbound-variable-function-name condition))
    (internal-undefined-function 
     (%%internal-undefined-function-function-name condition))
    (internal-end-of-file        
     (%%internal-end-of-file-function-name condition))
    (internal-simple-file-error  
     (%%internal-simple-file-error-function-name condition))
    (internal-simple-stream-error 
     (%%internal-simple-stream-error-function-name condition))))
)

#-(or clos pcl)
(progn

(DEFUN SIMPLE-CONDITION-FORMAT-STRING (CONDITION)
  (ETYPECASE CONDITION
    (SIMPLE-CONDITION  (%%SIMPLE-CONDITION-FORMAT-STRING  CONDITION))
    (SIMPLE-WARNING    (%%SIMPLE-WARNING-FORMAT-STRING    CONDITION))
    (SIMPLE-TYPE-ERROR (%%SIMPLE-TYPE-ERROR-FORMAT-STRING CONDITION))
    (SIMPLE-ERROR      (%%SIMPLE-ERROR-FORMAT-STRING      CONDITION))
    #+kcl(internal-simple-error
	  (%%internal-simple-error-format-string condition))
    #+kcl(internal-simple-program-error
	  (%%internal-simple-program-error-format-string condition))
    #+kcl(internal-simple-control-error
	  (%%internal-simple-control-error-format-string condition))
    #+kcl(internal-simple-file-error
	  (%%internal-simple-file-error-format-string condition))
    #+kcl(internal-simple-stream-error
	  (%%internal-simple-stream-error-format-string condition))))

(DEFUN SIMPLE-CONDITION-FORMAT-ARGUMENTS (CONDITION)
  (ETYPECASE CONDITION
    (SIMPLE-CONDITION  (%%SIMPLE-CONDITION-FORMAT-ARGUMENTS  CONDITION))
    (SIMPLE-WARNING    (%%SIMPLE-WARNING-FORMAT-ARGUMENTS    CONDITION))
    (SIMPLE-TYPE-ERROR (%%SIMPLE-TYPE-ERROR-FORMAT-ARGUMENTS CONDITION))
    (SIMPLE-ERROR      (%%SIMPLE-ERROR-FORMAT-ARGUMENTS      CONDITION))
    #+kcl(internal-simple-error
	  (%%internal-simple-error-format-arguments condition))
    #+kcl(internal-simple-program-error
	  (%%internal-simple-program-error-format-arguments condition))
    #+kcl(internal-simple-control-error
	  (%%internal-simple-control-error-format-arguments condition))
    #+kcl(internal-simple-file-error
	  (%%internal-simple-file-error-format-arguments condition))
    #+kcl(internal-simple-stream-error
	  (%%internal-simple-stream-error-format-arguments condition))))

(defun simple-condition-class-p (type)
  (member type '(SIMPLE-CONDITION SIMPLE-WARNING SIMPLE-TYPE-ERROR SIMPLE-ERROR
		 #+kcl internal-simple-error
		 #+kcl internal-simple-program-error
		 #+kcl internal-simple-control-error
		 #+kcl internal-simple-file-error
		 #+kcl internal-simple-stream-error)))
)

#+(or clos pcl)
(progn
(defvar *simple-condition-class* (find-class 'simple-condition))

(defun simple-condition-class-p (TYPE)
  (when (symbolp TYPE)
    (setq TYPE (find-class TYPE)))
  (and (typep TYPE 'standard-class)
       (member *simple-condition-class* 
	       (#+pcl pcl::class-precedence-list
		#-pcl clos::class-precedence-list
		  type))))
)


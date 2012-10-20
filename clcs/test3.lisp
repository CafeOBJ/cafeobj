(IN-PACKAGE "CONDITIONS")

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

(define-condition internal-undefined-function 
    (#+(or clos pcl) internal-error undefined-function)
  #-(or clos pcl)
  ((function-name nil))
  #+(or clos pcl)
  ()
  #-(or clos pcl)(:conc-name %%internal-undefined-function-)
  #-(or clos pcl)(:REPORT (LAMBDA (CONDITION STREAM)
			    (when (internal-error-function-name condition)
			      (format stream "Error in ~S [or a callee]: "
				      (internal-error-function-name condition)))
			    (FORMAT STREAM "The function ~S is undefined."
				    (CELL-ERROR-NAME CONDITION)))))

(define-condition internal-end-of-file 
    (#+(or clos pcl) internal-error end-of-file)
  #-(or clos pcl)
  ((function-name nil))
  #+(or clos pcl)
  ()
  #-(or clos pcl)(:conc-name %%internal-end-of-file-)
  #-(or clos pcl)(:REPORT (LAMBDA (CONDITION STREAM)
			    (when (internal-error-function-name condition)
			      (format stream "Error in ~S [or a callee]: "
				      (internal-error-function-name condition)))
			    (FORMAT STREAM "Unexpected end of file on ~S."
				    (STREAM-ERROR-STREAM CONDITION)))))

(define-condition internal-simple-file-error
    (#+(or clos pcl) internal-simple-error file-error)
  #-(or clos pcl)
  ((function-name nil) format-string (format-arguments '()))
  #+(or clos pcl)
  ()
  #-(or clos pcl)(:conc-name %%internal-simple-file-error-)
  #-(or clos pcl)(:report internal-simple-error-printer))

(define-condition internal-simple-stream-error 
    (#+(or clos pcl) internal-simple-error stream-error)
  #-(or clos pcl)
  ((function-name nil) format-string (format-arguments '()))
  #+(or clos pcl)
  ()
  #-(or clos pcl)(:conc-name %%internal-simple-stream-error-)
  #-(or clos pcl)(:report internal-simple-error-printer))

(in-package "conditions")

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
     (%%internal-simple-error-function-name condition))
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


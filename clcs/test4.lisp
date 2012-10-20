(IN-PACKAGE "CONDITIONS")

(define-condition internal-unbound-variable 
    (#+(or clos pcl) internal-error unbound-variable) #-(or clos pcl) ((function-name nil))
    #+(or clos pcl) ()  #-(or clos pcl)(:conc-name %%internal-unbound-variable-)
    #-(or clos pcl)(:REPORT (LAMBDA (CONDITION STREAM)
			    (when (internal-error-function-name condition)
			      (format stream "Error in ~S [or a callee]: "
				      (internal-error-function-name condition)))
			    (FORMAT STREAM "The variable ~S is unbound."
				    (CELL-ERROR-NAME CONDITION)))))


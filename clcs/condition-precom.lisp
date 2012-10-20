;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: "CONDITIONS"; Base: 10 -*-

(in-package "CONDITIONS" :USE '("LISP" #+(and clos (not pcl)) "CLOS" #+pcl "PCL"))

#-(or lucid excl genera)
(progn

#+pcl
(eval-when (compile load eval)
(defun exercise-condition-classes ()
  (let ((gfuns nil))
    (dolist (name '(make-instance
		    initialize-instance
		    shared-initialize
		    print-object))
      (push (pcl::gdefinition name) gfuns))
    (labels ((do-class (class)
	       (dolist (gfun (pcl::specializer-generic-functions class))
		 (pushnew gfun gfuns))
	       (dolist (dsub (pcl::class-direct-subclasses class))
		 (do-class dsub))))
      (do-class (find-class 'condition)))
    (mapc #'pcl::exercise-generic-function gfuns))
  nil)
)

#+pcl
(progn
(eval-when (compile)
(exercise-condition-classes)
)

(pcl::precompile-random-code-segments clcs)

(eval-when (load eval)
(exercise-condition-classes)
)
)

#+kcl (install-clcs-symbols)

)

(defun dsys::retry-operation (function retry-string)
  (loop (with-simple-restart (retry retry-string)
	  (return-from dsys::retry-operation
	    (funcall function)))))

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

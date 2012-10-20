(defun jamie-load-clcs (&optional (mode :compiled))
  (let ((files (list 
		"package"
		"precom"
		"macros"
		"restart"
		"handler"
		"debugger"
		"conditions"
		"condition-definitions"
		"kcl-cond"
		"top-patches"
		"install")))
    (when (eql :compile mode)
	  (load "package.lisp")
	  (load "precom.lisp"))
    (mapc #'(lambda (file)
	      (ecase mode
		     (:interpreted (load (format nil "~A.lisp" file)))
		     (:compiled (load (format nil "~A.o" file)))
		     (:compile (compile-file (format nil "~A.lisp" file)))))
	  files)))


;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: "CONDITIONS"; Base: 10 -*-

(in-package "CONDITIONS" :USE '("LISP" #+(and clos (not pcl)) "CLOS" #+pcl "PCL"))

#+kcl
(eval-when (compile load eval)
(when (fboundp 'remove-clcs-symbols)
  (remove-clcs-symbols))
)

;DEFINE-CONDITION
;MAKE-CONDITION
;condition printing
;(define-condition CONDITION ...)
;CONDITIONP
;CONDITION-CLASS-P
;SIMPLE-CONDITION-P
;SIMPLE-CONDITION-CLASS-P

#-(or clos pcl)
(progn
(DEFUN CONDITION-PRINT (CONDITION STREAM DEPTH)
  DEPTH ;ignored
  (COND (*PRINT-ESCAPE*
         (FORMAT STREAM "#<~S.~D>" (TYPE-OF CONDITION) (UNIQUE-ID CONDITION)))
        (T
         (CONDITION-REPORT CONDITION STREAM))))

(DEFSTRUCT (CONDITION :CONC-NAME
                      (:CONSTRUCTOR |Constructor for CONDITION|)
                      (:PREDICATE NIL)
                      (:PRINT-FUNCTION CONDITION-PRINT))
  (-DUMMY-SLOT- NIL))

(EVAL-WHEN (EVAL COMPILE LOAD)

(DEFMACRO PARENT-TYPE     (CONDITION-TYPE) `(GET ,CONDITION-TYPE 'PARENT-TYPE))
(DEFMACRO SLOTS           (CONDITION-TYPE) `(GET ,CONDITION-TYPE 'SLOTS))
(DEFMACRO CONC-NAME       (CONDITION-TYPE) `(GET ,CONDITION-TYPE 'CONC-NAME))
(DEFMACRO REPORT-FUNCTION (CONDITION-TYPE) `(GET ,CONDITION-TYPE 'REPORT-FUNCTION))
(DEFMACRO MAKE-FUNCTION   (CONDITION-TYPE) `(GET ,CONDITION-TYPE 'MAKE-FUNCTION))

);NEHW-LAVE

(DEFUN CONDITION-REPORT (CONDITION STREAM)
  (DO ((TYPE (TYPE-OF CONDITION) (PARENT-TYPE TYPE)))
      ((NOT TYPE) (FORMAT STREAM "The condition ~A occurred." (TYPE-OF CONDITION)))
    (LET ((REPORTER (REPORT-FUNCTION TYPE)))
      (WHEN REPORTER
        (FUNCALL REPORTER CONDITION STREAM)
        (RETURN NIL)))))

(SETF (MAKE-FUNCTION   'CONDITION) '|Constructor for CONDITION|)

(DEFUN MAKE-CONDITION (TYPE &REST SLOT-INITIALIZATIONS)
  (LET ((FN (MAKE-FUNCTION TYPE)))
    (COND ((NOT FN) (ERROR 'SIMPLE-TYPE-ERROR
			   :DATUM TYPE
			   :EXPECTED-TYPE '(SATISFIES MAKE-FUNCTION)
			   :FORMAT-STRING "Not a condition type: ~S"
			   :FORMAT-ARGUMENTS (LIST TYPE)))
          (T (APPLY FN SLOT-INITIALIZATIONS)))))

(EVAL-WHEN (EVAL COMPILE LOAD) ;Some utilities that are used at macro expansion time

(DEFUN PARSE-NEW-AND-USED-SLOTS (SLOTS PARENT-TYPE)
  (LET ((NEW '()) (USED '()))
    (DOLIST (SLOT SLOTS)
      (IF (SLOT-USED-P (CAR SLOT) PARENT-TYPE)
          (PUSH SLOT USED)
          (PUSH SLOT NEW)))
    (VALUES NEW USED)))

(DEFUN SLOT-USED-P (SLOT-NAME TYPE)
  (COND ((EQ TYPE 'CONDITION) NIL)
        ((NOT TYPE) (ERROR "The type ~S does not inherit from CONDITION." TYPE))
        ((ASSOC SLOT-NAME (SLOTS TYPE)))
        (T
         (SLOT-USED-P SLOT-NAME (PARENT-TYPE TYPE)))))

);NEHW-LAVE

(DEFMACRO DEFINE-CONDITION (NAME (PARENT-TYPE) SLOT-SPECS &REST OPTIONS)
  (LET ((CONSTRUCTOR (LET ((*PACKAGE* *THIS-PACKAGE*)) ;Bind for the INTERN -and- the FORMAT
                       (INTERN (FORMAT NIL "Constructor for ~S" NAME)))))
    (LET ((SLOTS (MAPCAR #'(LAMBDA (SLOT-SPEC)
			     (IF (ATOM SLOT-SPEC) (LIST SLOT-SPEC) SLOT-SPEC))
			 SLOT-SPECS)))
      (MULTIPLE-VALUE-BIND (NEW-SLOTS USED-SLOTS)
          (PARSE-NEW-AND-USED-SLOTS SLOTS PARENT-TYPE)
	(LET ((CONC-NAME-P     NIL)
	      (CONC-NAME       NIL)
	      (REPORT-FUNCTION NIL)
	      (DOCUMENTATION   NIL))
	  (DO ((O OPTIONS (CDR O)))
	      ((NULL O))
	    (LET ((OPTION (CAR O)))
	      (CASE (CAR OPTION) ;Should be ECASE
		(:CONC-NAME (SETQ CONC-NAME-P T)
		 	    (SETQ CONC-NAME (CADR OPTION)))
		(:REPORT (SETQ REPORT-FUNCTION (IF (STRINGP (CADR OPTION))
						   `(LAMBDA (CONDITION STREAM)
						      (DECLARE (IGNORE CONDITION))
						      (WRITE-STRING ,(CADR OPTION) STREAM))
						   (CADR OPTION))))
		(:DOCUMENTATION (SETQ DOCUMENTATION (CADR OPTION)))
		(OTHERWISE (CERROR "Ignore this DEFINE-CONDITION option."
				   "Invalid DEFINE-CONDITION option: ~S" OPTION)))))
	  (IF (NOT CONC-NAME-P) (SETQ CONC-NAME (INTERN (FORMAT NIL "~A-" NAME) *PACKAGE*)))
          ;; The following three forms are compile-time side-effects. For now, they affect
          ;; the global environment, but with modified abstractions for PARENT-TYPE, SLOTS, 
          ;; and CONC-NAME, the compiler could easily make them local.
          (SETF (PARENT-TYPE NAME) PARENT-TYPE)
          (SETF (SLOTS NAME)       SLOTS)
          (SETF (CONC-NAME NAME)   CONC-NAME)
          ;; Finally, the expansion ...
          `(PROGN (DEFSTRUCT (,NAME
                              (:CONSTRUCTOR ,CONSTRUCTOR)
                              (:PREDICATE NIL)
			      (:COPIER NIL)
                              (:PRINT-FUNCTION CONDITION-PRINT)
                              (:INCLUDE ,PARENT-TYPE ,@USED-SLOTS)
                              (:CONC-NAME ,CONC-NAME))
                    ,@NEW-SLOTS)
		  (SETF (DOCUMENTATION ',NAME 'TYPE) ',DOCUMENTATION)
                  (SETF (PARENT-TYPE ',NAME) ',PARENT-TYPE)
                  (SETF (SLOTS ',NAME) ',SLOTS)
                  (SETF (CONC-NAME ',NAME) ',CONC-NAME)
                  (SETF (REPORT-FUNCTION ',NAME) ,(IF REPORT-FUNCTION `#',REPORT-FUNCTION))
                  (SETF (MAKE-FUNCTION ',NAME) ',CONSTRUCTOR)
                  ',NAME))))))

(defun conditionp (object)
  (typep object 'condition))

(defun condition-class-p (object)
  (and (symbolp object)
       (MAKE-FUNCTION object)))

)



#+(or clos pcl)
(progn

(eval-when (compile load eval)
(defvar *condition-class-list* nil) ; list of (class-name initarg1 type1...)
)

(DEFMACRO DEFINE-CONDITION (NAME PARENT-LIST SLOT-SPECS &REST OPTIONS)
  (let* ((REPORT-FUNCTION nil)
	 (DOCUMENTATION nil))
    (DO ((O OPTIONS (CDR O)))
	((NULL O))
      (LET ((OPTION (CAR O)))
	(CASE (CAR OPTION)
	  (:REPORT (SETQ REPORT-FUNCTION (IF (STRINGP (CADR OPTION))
					     `(LAMBDA (CONDITION STREAM)
					        (DECLARE (IGNORE CONDITION))
					        (WRITE-STRING ,(CADR OPTION) STREAM))
					     (CADR OPTION))))
	  (:DOCUMENTATION (SETQ DOCUMENTATION (CADR OPTION)))
	  (OTHERWISE (CERROR "Ignore this DEFINE-CONDITION option."
			     "Invalid DEFINE-CONDITION option: ~S" OPTION)))))
    `(progn
       (eval-when (compile)
	 #+pcl (setq pcl::*defclass-times* '(compile load eval)))
       (defclass ,name ,parent-list
	 ,slot-specs)
       (eval-when (compile load eval)
	 (pushnew '(,name ,parent-list
		    ,@(mapcan #'(lambda (slot-spec)
				  (let* ((ia (getf (cdr slot-spec) ':initarg)))
				    (when ia
				      (list
				       (cons ia
					     (or (getf (cdr slot-spec) ':type)
						 t))))))
		       SLOT-SPECS))
		  *condition-class-list*)
	 #+kcl (setf (get ',name #+akcl 'si::s-data #-akcl 'si::is-a-structure) nil)
	 (setf (get ',name 'documentation) ',documentation))
      ,@(when REPORT-FUNCTION
	   `((DEFMETHOD PRINT-OBJECT ((X ,NAME) STREAM)
	       (IF *PRINT-ESCAPE*
		   (CALL-NEXT-METHOD)
		   (,REPORT-FUNCTION X STREAM)))))
      ',NAME)))

(eval-when (compile load eval)
(define-condition condition ()
  ())

#+pcl
(when (fboundp 'pcl::proclaim-incompatible-superclasses)
  (mapc
   #'pcl::proclaim-incompatible-superclasses
   '((condition pcl::metaobject))))
)

(defun conditionp (object)
  (typep object 'condition))

(DEFMETHOD PRINT-OBJECT ((X condition) STREAM)
  (IF *PRINT-ESCAPE* 
      (FORMAT STREAM "#<~S.~D>" (class-name (class-of x)) (UNIQUE-ID x))
      (FORMAT STREAM "The condition ~A occurred." (TYPE-OF x))))

(defvar *condition-class* (find-class 'condition))

(defun condition-class-p (TYPE)
  (when (symbolp TYPE)
    (setq TYPE (find-class TYPE)))
  (and (typep TYPE 'standard-class)
       (member *condition-class* 
	       (#+pcl pcl::class-precedence-list
		#-pcl clos::class-precedence-list
		  type))))

(DEFUN MAKE-CONDITION (TYPE &REST SLOT-INITIALIZATIONS)
  (unless (condition-class-p TYPE)
    (ERROR 'SIMPLE-TYPE-ERROR
	   :DATUM TYPE
	   :EXPECTED-TYPE '(SATISFIES condition-class-p)
	   :FORMAT-STRING "Not a condition type: ~S"
	   :FORMAT-ARGUMENTS (LIST TYPE)))
  (apply #'make-instance TYPE SLOT-INITIALIZATIONS))

)

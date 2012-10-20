;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: "CONDITIONS"; Base: 10 -*-

(IN-PACKAGE "CONDITIONS")

;;; Unique Ids

(DEFVAR *UNIQUE-ID-TABLE* (MAKE-HASH-TABLE))
(DEFVAR *UNIQUE-ID-COUNT* -1)

(DEFUN UNIQUE-ID (OBJ)
  "Generates a unique integer ID for its argument."
  (OR (GETHASH OBJ *UNIQUE-ID-TABLE*)
      (SETF (GETHASH OBJ *UNIQUE-ID-TABLE*) (INCF *UNIQUE-ID-COUNT*))))

;;; Miscellaneous Utilities

(EVAL-WHEN (EVAL COMPILE LOAD)

(DEFUN PARSE-KEYWORD-PAIRS (LIST KEYS)
  (DO ((L LIST (CDDR L))
       (K '() (LIST* (CADR L) (CAR L) K)))
      ((OR (NULL L) (NOT (MEMBER (CAR L) KEYS)))
       (VALUES (NREVERSE K) L))))

(DEFMACRO WITH-KEYWORD-PAIRS ((NAMES EXPRESSION &OPTIONAL KEYWORDS-VAR) &BODY FORMS)
  (LET ((TEMP (MEMBER '&REST NAMES)))
    (UNLESS (= (LENGTH TEMP) 2) (ERROR "&REST keyword is ~:[missing~;misplaced~]." TEMP))
    (LET ((KEY-VARS (LDIFF NAMES TEMP))
          (KEY-VAR (OR KEYWORDS-VAR (GENSYM)))
          (REST-VAR (CADR TEMP)))
      (LET ((KEYWORDS (MAPCAR #'(LAMBDA (X) (INTERN (STRING X) (FIND-PACKAGE "KEYWORD")))
			      KEY-VARS)))
        `(MULTIPLE-VALUE-BIND (,KEY-VAR ,REST-VAR)
             (PARSE-KEYWORD-PAIRS ,EXPRESSION ',KEYWORDS)
           (LET ,(MAPCAR #'(LAMBDA (VAR KEYWORD) `(,VAR (GETF ,KEY-VAR ,KEYWORD)))
                                 KEY-VARS KEYWORDS)
             ,@FORMS))))))

);NEHW-LAVE

;;; Restarts

(DEFVAR *RESTART-CLUSTERS* '())

(DEFUN COMPUTE-RESTARTS ()
  #+kcl (nconc (mapcan #'copy-list *RESTART-CLUSTERS*) (kcl-top-restarts))
  #-kcl (mapcan #'copy-list *RESTART-CLUSTERS*))

(DEFUN RESTART-PRINT (RESTART STREAM DEPTH)
  (DECLARE (IGNORE DEPTH))
  (IF *PRINT-ESCAPE*
      (FORMAT STREAM "#<~S.~D>" (TYPE-OF RESTART) (UNIQUE-ID RESTART))
      (RESTART-REPORT RESTART STREAM)))

(DEFSTRUCT (RESTART (:PRINT-FUNCTION RESTART-PRINT))
  NAME
  FUNCTION
  REPORT-FUNCTION
  INTERACTIVE-FUNCTION)

#+kcl
(progn
(defvar *kcl-top-restarts* nil)

(defun make-kcl-top-restart (quit-tag)
  (make-restart :name 'abort
		:function #'(lambda () (throw (car (list quit-tag)) quit-tag))
		:report-function 
		#'(lambda (stream) 
		    (let ((b-l (if (eq quit-tag si::*quit-tag*)
				   si::*break-level*
				   (car (or (find quit-tag si::*quit-tags*
						  :key #'cdr)
					    '(:not-found))))))
		      (cond ((eq b-l :not-found)
			     (format stream "Return to ? level."))
			    ((null b-l)
			     (format stream "Return to top level."))
			    (t
			     (format stream "Return to break level ~D."
				     (length b-l))))))
		:interactive-function nil))

(defun find-kcl-top-restart (quit-tag)
  (cdr (or (assoc quit-tag *kcl-top-restarts*)
	   (car (push (cons quit-tag (make-kcl-top-restart quit-tag))
		      *kcl-top-restarts*)))))

(defun kcl-top-restarts ()
  (let* ((old-tags (mapcan #'(lambda (e) (when (cdr e) (list (cdr e))))
			   si::*quit-tags*))
	 (tags (if si::*quit-tag* (cons si::*quit-tag* old-tags) old-tags))
	 (restarts (mapcar #'find-kcl-top-restart tags)))
    (setq *kcl-top-restarts* (mapcar #'cons tags restarts))
    restarts))
)  

(DEFUN RESTART-REPORT (RESTART STREAM)
  (FUNCALL (OR (RESTART-REPORT-FUNCTION RESTART)
               (LET ((NAME (RESTART-NAME RESTART)))
		 #'(LAMBDA (STREAM)
		     (IF NAME (FORMAT STREAM "~S" NAME)
			      (FORMAT STREAM "~S" RESTART)))))
           STREAM))

(DEFMACRO RESTART-BIND (BINDINGS &BODY FORMS)
  `(LET ((*RESTART-CLUSTERS* (CONS (LIST ,@(MAPCAR #'(LAMBDA (BINDING)
						       `(MAKE-RESTART
							  :NAME     ',(CAR BINDING)
							  :FUNCTION ,(CADR BINDING)
							  ,@(CDDR BINDING)))
						   BINDINGS))
				   *RESTART-CLUSTERS*)))
     ,@FORMS))

(DEFUN FIND-RESTART (NAME)
  (DOLIST (RESTART-CLUSTER *RESTART-CLUSTERS*)
    (DOLIST (RESTART RESTART-CLUSTER)
      (WHEN (OR (EQ RESTART NAME) (EQ (RESTART-NAME RESTART) NAME))
	(RETURN-FROM FIND-RESTART RESTART))))
  #+kcl 
  (let ((RESTART-CLUSTER (kcl-top-restarts)))
    (DOLIST (RESTART RESTART-CLUSTER)
      (WHEN (OR (EQ RESTART NAME) (EQ (RESTART-NAME RESTART) NAME))
	(RETURN-FROM FIND-RESTART RESTART)))))
  
(DEFUN INVOKE-RESTART (RESTART &REST VALUES)
  (LET ((REAL-RESTART (OR (FIND-RESTART RESTART)
			  (ERROR "Restart ~S is not active." RESTART))))
    (APPLY (RESTART-FUNCTION REAL-RESTART) VALUES)))

(DEFUN INVOKE-RESTART-INTERACTIVELY (RESTART)
  (LET ((REAL-RESTART (OR (FIND-RESTART RESTART)
			  (ERROR "Restart ~S is not active." RESTART))))
    (APPLY (RESTART-FUNCTION REAL-RESTART)
	   (LET ((INTERACTIVE-FUNCTION
		   (RESTART-INTERACTIVE-FUNCTION REAL-RESTART)))
	     (IF INTERACTIVE-FUNCTION
		 (FUNCALL INTERACTIVE-FUNCTION)
		 '())))))

(DEFMACRO RESTART-CASE (EXPRESSION &BODY CLAUSES)
  (FLET ((TRANSFORM-KEYWORDS (&KEY REPORT INTERACTIVE)
	   (LET ((RESULT '()))
	     (WHEN REPORT
	       (SETQ RESULT (LIST* (IF (STRINGP REPORT)
				       `#'(LAMBDA (STREAM)
					    (WRITE-STRING ,REPORT STREAM))
				       `#',REPORT)
				   :REPORT-FUNCTION
				   RESULT)))
	     (WHEN INTERACTIVE
	       (SETQ RESULT (LIST* `#',INTERACTIVE
				   :INTERACTIVE-FUNCTION
				   RESULT)))
	     (NREVERSE RESULT))))
    (LET ((BLOCK-TAG (GENSYM))
	  (TEMP-VAR  (GENSYM))
	  (DATA
	    (MAPCAR #'(LAMBDA (CLAUSE)
			(WITH-KEYWORD-PAIRS ((REPORT INTERACTIVE &REST FORMS)
					     (CDDR CLAUSE))
			  (LIST (CAR CLAUSE)			   ;Name=0
				(GENSYM)			   ;Tag=1
				(TRANSFORM-KEYWORDS :REPORT REPORT ;Keywords=2
						    :INTERACTIVE INTERACTIVE)
				(CADR CLAUSE)			   ;BVL=3
				FORMS)))			   ;Body=4
		    CLAUSES)))
      `(BLOCK ,BLOCK-TAG
	 (LET ((,TEMP-VAR NIL))
	   (TAGBODY
	     (RESTART-BIND
	       ,(MAPCAR #'(LAMBDA (DATUM)
			    (LET ((NAME (NTH 0 DATUM))
				  (TAG  (NTH 1 DATUM))
				  (KEYS (NTH 2 DATUM)))
			      `(,NAME #'(LAMBDA (&REST TEMP)
					  #+LISPM (SETQ TEMP (COPY-LIST TEMP))
					  (SETQ ,TEMP-VAR TEMP)
					  (GO ,TAG))
				,@KEYS)))
			DATA)
	       (RETURN-FROM ,BLOCK-TAG ,EXPRESSION))
	     ,@(MAPCAN #'(LAMBDA (DATUM)
			   (LET ((TAG  (NTH 1 DATUM))
				 (BVL  (NTH 3 DATUM))
				 (BODY (NTH 4 DATUM)))
			     (LIST TAG
				   `(RETURN-FROM ,BLOCK-TAG
				      (APPLY #'(LAMBDA ,BVL ,@BODY)
					     ,TEMP-VAR)))))
		       DATA)))))))

(DEFMACRO WITH-SIMPLE-RESTART ((RESTART-NAME FORMAT-STRING
					     &REST FORMAT-ARGUMENTS)
			       &BODY FORMS)
  `(RESTART-CASE (PROGN ,@FORMS)
     (,RESTART-NAME ()
        :REPORT (LAMBDA (STREAM)
		  (FORMAT STREAM ,FORMAT-STRING ,@FORMAT-ARGUMENTS))
      (VALUES NIL T))))

(DEFUN ABORT          ()      (INVOKE-RESTART 'ABORT)
       			      (ERROR 'ABORT-FAILURE))
(DEFUN CONTINUE       ()      (INVOKE-RESTART 'CONTINUE))
(DEFUN MUFFLE-WARNING ()      (INVOKE-RESTART 'MUFFLE-WARNING))
(DEFUN STORE-VALUE    (VALUE) (INVOKE-RESTART 'STORE-VALUE VALUE))
(DEFUN USE-VALUE      (VALUE) (INVOKE-RESTART 'USE-VALUE   VALUE))

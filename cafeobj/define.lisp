;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
#|==============================================================================
                            System: CHAOS
                           Module: cafeobj
                          File: define.lisp
==============================================================================|#
(in-package :chaos)
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))


;;; *****************************************************
;;; On line document for commands, declarations or others 
;;; *****************************************************

(defvar *cafeobj-doc-db* (make-hash-table :test #'equal))
(defvar *cafeobj-alias-db* (make-hash-table :test #'equal))

(defstruct (oldoc (:print-function print-online-document))
  (key        ""  :type string)		; 
  (doc-string ""  :type string)		; document string of commad/declaration
  (doc-title  ""  :type string)         ; title 
  (doc-ex     ""  :type string)         ; examples
  (mdkey      ""  :type string)         ; key written to reference manual
  (names      nil :type list)		;
  (cache nil)				; formatted doc cache for online help
  )

(defun print-online-document (doc &optional (stream *standard-output*) &rest ignore)
  (declare (ignore ignore))
  (format stream "~%*** key    : ~a" (oldoc-key doc))
  (format stream "~&doc-title  : ~a" (oldoc-doc-title doc))
  (format stream "~&mdkey      : ~a" (oldoc-mdkey doc))
  (format stream "~&doc-string : ~a" (oldoc-doc-string doc))
  (format stream "~&doc-ex     : ~a" (oldoc-doc-ex doc))
  (format stream "~&names      : ~a" (oldoc-names doc))
  (format stream "~&cache      : ~a" (oldoc-cache doc)))

(defun make-oldoc-key (question)
  (reduce #'(lambda (x y) (concatenate 'string x y)) question))
(defun make-oldoc-name (question)
  (format nil "~{~a~^ ~}" question))


(defun find-doc-entry (question)
  ;; first try whether it is already a key
  (let ((docref (gethash question *cafeobj-alias-db*)))
    (if docref
	(gethash docref *cafeobj-doc-db*)
      ;, next make a key from the question and check whether that is found
      (let* ((key (make-oldoc-key question))
	     (docref (gethash key *cafeobj-alias-db*)))
	(if docref (gethash docref *cafeobj-doc-db*)
	  ;; finally, search for similar names
	  (let* ((nstr (make-oldoc-name question))
		 (similar-keys nil) (l (length nstr)))
	    (maphash #'(lambda (k v)
			 (let ((subl nil))
			   (dolist (n (oldoc-names v))
			     (if (and (>= (length n) l)
				      (string-equal nstr (subseq n 0 l)))
				 (push (concatenate 'string "\"" n "\"") subl)))
			   (if subl
			       (push (cons k subl) similar-keys)))) 
		     *cafeobj-doc-db*)
	    ;; if only one similar name is found, return the entry for it
	    (if (= 1 (length similar-keys))
		(gethash (car (car similar-keys)) *cafeobj-doc-db*)
	      (apply #'append (map 'list 'cdr similar-keys)))))))))

(defun get-document-string (key &optional (raw nil))
  (let ((doc (find-doc-entry key)))
    (if (not (listp doc))
	(if (not raw)
	    (or (oldoc-cache doc)
		(let (outstr (exstr (oldoc-doc-ex doc)))
		  (setq outstr (format nil "~a~2%~a~%" (oldoc-doc-title doc) (oldoc-doc-string doc)))
		  (if (not (string-equal exstr ""))
		      (setq outstr (format nil "~a(Examples available)~2%" outstr)))
		  (setf (oldoc-cache doc) 
			(format-markdown outstr))))
	  (format nil "## ~a ## {#~a}~2%~a~2%"
		  (oldoc-doc-title doc) (oldoc-mdkey doc) (oldoc-doc-string doc)))
      (progn 
	(if (and doc (not raw))
	    (format t "Did you mean one of ~a~%" doc))
	nil))))

(defun get-example-string (key &optional (raw nil))
  (let ((doc (find-doc-entry key)))
    (if (not (listp doc))
	(let ((exstr (oldoc-doc-ex doc)))
	  (if (not (string-equal exstr ""))
	      (if (not raw)
		  (format-markdown (format nil "Example(s) for ~a~2%~a~%" (oldoc-doc-title doc) exstr))
		(format nil "### Example ###~2%~a~2%" exstr))
	    (if (not raw)
		"no examples available" 
	      nil)))
      (progn
	(if (and doc (not raw))
	    (format t "Did you mean one of ~a~%" doc))
	nil))))

(defun show-doc-entries ()
  (let ((keys nil))
    (maphash #'(lambda (k v) (declare (ignore v)) (push k keys)) *cafeobj-doc-db*)
    (setq keys (sort keys #'string<=))
    (dolist (key keys)
      (let ((oldoc (get-document-string key)))
	(format t "~s" oldoc)))))

;;;
;;; search for an arbitrary regexp in all doc-strings, and return
;;; string that lists all possible matches
;;;
(defun search-all-doc (what)
  ; what is the list of arguments to the ?apropos command
  (let ((re (car what))
	(retstr ""))
    (if re (let ((re (cl-ppcre:create-scanner re :case-insensitive-mode :multi-line-mode))
		 (matching-docs nil))
	     (maphash #'(lambda (key oldoc)
			  (declare (ignore key))
			  (let* ((str (oldoc-doc-string oldoc))
				 (found (cl-ppcre:scan re str)))
			    (when found
			      (push (oldoc-doc-title oldoc) matching-docs))))
		      *cafeobj-doc-db*)
	     ; create the return string from the list of found keys
	     (when matching-docs
	       (setq retstr (format nil "Found the following matches:~% . ~{~a~^~% . ~}" matching-docs)))))
    (if (string= retstr "")
	(setq retstr (format nil "No matches found!~%")))
    retstr))

;;;
;;;
;;; register-online-help : names doc 
;;;

(defun make-doc-key-from-string (str)
  (when (atom str)
    (setq str (list str)))
  (let ((keys nil))
    (dolist (s str)
      (let ((keyl (remove "" (parse-with-delimiter s #\space))))
	(push (make-oldoc-key keyl) keys)))
    keys))

(defun register-online-help (mainname aliasnames title mdkey doc example)
  (unless doc (return-from register-online-help nil))
  (unless (stringp doc) (return-from register-online-help nil))
  ; for each key generated from any name we generate an entry
  ; from that key to each key generated from the mainname
  ; (although there should be only one mainname and mainkey (?)
  (dolist (mainkey (make-doc-key-from-string mainname))
    (dolist (name (cons mainname aliasnames))
      (dolist (key (make-doc-key-from-string name))
	(setf (gethash key *cafeobj-alias-db*) mainkey))))
  (dolist (key (make-doc-key-from-string mainname))
    ; if the tile is not given, we use the mainname enclosed in ` `
    ; if the mdkey is not given, we use the mainname as is
    (setf (gethash key *cafeobj-doc-db*) 
	  (make-oldoc :key key
		      :doc-string doc
		      :doc-title (or title
				     (concatenate 'string "`" mainname "`"))
		      :mdkey (or mdkey mainname)
		      :doc-ex (or example "")
		      :names (cons mainname aliasnames)))))

(defparameter .md-remove-hash-hash. #~s/##//)
(defparameter .md-remove-link. #~s/{#.*}//)
(defparameter .md-remove-link2. #~s/\(#.+\)//)
(defparameter .md-remove-code-sign. #~s/~~//)
(defparameter .md-replace-tilde. #~s/~/*/)
(defparameter .md-replace-bq. #~s/`/'/)

(defun format-markdown (str)
  (funcall .md-replace-bq.
	   (funcall .md-replace-tilde.
		    (funcall .md-remove-code-sign.
			     (funcall .md-remove-link2.
				      (funcall .md-remove-link.
					       (funcall .md-remove-hash-hash. str)))))))

;;; ******
;;; DEFINE : define command or declaration
;;; ******

(defvar *cafeobj-top-commands* (make-hash-table :test #'equal))
(defvar *cafeobj-declarations* (make-hash-table :test #'equal))

(defstruct (comde (:print-function print-comde))
  (key       ""  :type string)		; command/declaration keyword
  (type      nil :type symbol)		; command or declaration
  (category  nil :type symbol)		; kind of command/declaration
  (parser    nil :type symbol)		; parser function
  (evaluator nil :type symbol)		; evaluator function
  )

(defparameter .valid-comde-types. '(:top :inner-module :doc-only))
(defparameter .valid-decl-categories. 
    '(:decl-toplevel			; toplevel declaration, such as 'module', 'view', e.t.c.
					; i.e., declarations which can apper at toplevel.
      :signature			; signature part of module body, such as 'op' '[', e.t.c
      :axiom				; axiom part of mdoule body, such as 'eq, ceq', e.t.c
      :ignore				; comments, dot (.), lisp, ev, e.t.c.
      :import				; import part of module body, such as 'protecting'
      :misc
      ))

(defparameter .valid-com-categories.
    '(:decl-toplevel	       ; toplevel declaration, such as 'module', 'view', e.t.c.
      :checker		       ; check command
      :module		       ; apply some modifications to a module, such as regularize
      :rewrite		       ; commands related to rewriting, such as 'reduce', 'execute', e.t.c.
      :parse		       ; commands related to parsing terms, such as 'parse', e.t.c
      :inspect		       ; commands inspecting modules, terms, such as 'show', 'match', e.t.c
      :module-element	       ; declarations which can apper when a module is open.
      :proof		       ; commands related to proof stuff, such as 'open', 'apply, e.t.c.
      :switch		       ; 'set' commands
      :system		       ; various system related commands, such as 'protect', 'reset', e.t.c.
      :library		       ; library related commands, such as 'autoload', 'provide', e.t.c.
      :help		       ; '?', '??' 
      :io		       ; 'input', 'save', e.t.c.
      :misc		       ; 
      ))

(defun print-comde (me &optional (stream *standard-output*) &rest ignore)
  (declare (ignore ignore))
  (format stream "~%** key         : ~a" (comde-key me))
  (format stream "~%   type        : ~a" (comde-type me))
  (format stream "~%   category    : ~a" (comde-category me))
  (format stream "~%   parser      : ~a" (comde-parser me))
  (format stream "~%   evaluator   : ~a" (comde-evaluator me)))

;;;
;;; get-command-info
;;;
(defun get-command-info (key)
  (gethash key *cafeobj-top-commands*))


(defun show-top-entries ()
  (let ((keys nil))
    (maphash #'(lambda (k v) (declare (ignore v)) (push k keys)) *cafeobj-top-commands*)
    (setq keys (sort keys #'string<=))
    (dolist (key keys)
      (format t "~s" (get-command-info key)))))

;;;
;;; get-decl-info
;;;
(defun get-decl-info (key)
  (gethash key *cafeobj-declarations*))

(defun show-decl-entries ()
  (let ((keys nil))
    (maphash #'(lambda (k v) (declare (ignore v)) (push k keys)) *cafeobj-declarations*)
    (setq keys (sort keys #'string<=))
    (dolist (key keys)
      (format t "~s" (get-decl-info key)))))

;;;
;;; DEFINE
;;; 
(defmacro define ((&rest keys) &key (type :top)
				    (category :misc)
				    (parser nil)
				    (evaluator 'eval-ast)
				    (doc nil)
				    (title nil)
				    (example nil)
				    (mdkey nil))
    (case type
      (:top (unless (member category .valid-com-categories.)
	      (error "Internal error, invalid category ~s" category)))
      (:inner-module (unless (member category .valid-decl-categories.)
			(error "Internal error, invalid category ~s" category)))
      (:doc-only)
      (:otherwise (error "Internal error, invalid type ~s" type)))
    (unless (eq type :doc-only)
      (unless (fboundp parser) (warn "no parser ~s" parser))
      (unless (fboundp evaluator) (warn "no evaluator ~s" evaluator)))
    ;;
    `(progn
       (unless (eq ,type :doc-only)
	 (let ((hash (if (or (eq ,type :top)
			     (eq ,category :decl-toplevel))
			 *cafeobj-top-commands*
		       *cafeobj-declarations*)))
	   (dolist (key ',keys)
	     (setf (gethash key hash) (make-comde :key key
						  :type ',type
						  :category ',category
						  :parser ',parser
						  :evaluator ',evaluator)))))
       ;; set online help
       (register-online-help (car ',keys) (cdr ',keys) ',title ',mdkey ',doc ',example)))

(defun print-comde-usage (com)
  (format t "~&[Usage] ~s, not yet" com))


;;;
;;; Export
;;; export document string to a file.
;;;
(defvar .out-done. (make-hash-table :test #'equal))

(defun export-refman (&optional (output "manual/md/reference.md"))
  (clrhash .out-done.)
  (let (doc docex keys)
    (with-open-file (out output :direction :output :if-exists :supersede :if-does-not-exist :create)
      (maphash #'(lambda (k doc) (declare (ignore doc)) (push k keys)) *cafeobj-doc-db*)
      (setq keys (sort keys #'string<=))
      (dolist (key keys)
	(setq doc (get-document-string key t))
	(unless doc
	  (error "The document string not found for ~s." key))
	(setq docex (get-example-string key t))
	(if docex
	    (setq doc (concatenate 'string doc docex)))
	(unless (gethash key .out-done.)
	  (format out "~a" doc)
	  (setf (gethash key .out-done.) t))))))

;;;
;;; show-undocumented
;;; list up undocumented, i.e. each keyword in *cafeobj-doc-db* which has no doc-string in 
;;; its oldoc. 
;;;
(defparameter .todo. #~m/TODO/)

(defun show-undocumented (&rest ignore)
  (declare (ignore ignore))
  (let ((docs nil))
    (maphash #'(lambda (key oldoc)
		 (declare (ignore key))
		 (let* ((str (oldoc-doc-string oldoc))
			(doc (cl-ppcre:split "\\s+" str)))
		   (when (or (null doc)
			     (null (cdr doc))
			     (funcall .todo. str))
		     (push oldoc docs))))
	     *cafeobj-doc-db*)
    (setq docs (sort docs #'string<= :key #'oldoc-key))
    (format t "~%The following commands/declarations/concepts are not yet documented.")
    (dolist (doc docs)
      (format t "~%** key   : ~s" (oldoc-key doc))
      (format t "~&   names : ~s" (oldoc-names doc)))))

;;; EOF

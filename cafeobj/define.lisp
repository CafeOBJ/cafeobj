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

(defstruct (oldoc (:print-function print-online-document))
  (key        ""  :type string)		; 
  (doc-string ""  :type string)		; document string of commad/declaration
  (names      nil :type list)		;
  (cache nil)				; formatted doc cache
  )

(defun print-online-document (doc &optional (stream *standard-output*) &rest ignore)
  (declare (ignore ignore))
  (format stream "~%*** key    : ~a" (oldoc-key doc))
  (format stream "~&doc-string : ~a" (oldoc-doc-string doc))
  (format stream "~&name       : ~a" (oldoc-names doc))
  (format stream "~&cache      : ~a" (oldoc-cache doc)))

(defun get-document-string (key &optional (raw nil))
  (let ((doc (gethash key *cafeobj-doc-db*)))
    (if doc
	(if (not raw)
	    (or (oldoc-cache doc)
		(setf (oldoc-cache doc) (format-description (oldoc-doc-string doc))))
	  (oldoc-doc-string doc))
      nil)))

(defun show-doc-entries ()
  (let ((keys nil))
    (maphash #'(lambda (k v) (declare (ignore v)) (push k keys)) *cafeobj-doc-db*)
    (setq keys (sort keys #'string<=))
    (dolist (key keys)
      (let ((oldoc (get-document-string key)))
	(format t "~s" oldoc)))))

;;;
;;; register-online-help : names doc 
;;;

(defun make-doc-key-from-string (str)
  (when (atom str)
    (setq str (list str)))
  (let ((keys nil))
    (dolist (s str)
      (let ((keyl (remove "" (parse-with-delimiter s #\space))))
	(push (reduce #'(lambda (x y) (concatenate 'string x y)) keyl) keys)))
    keys))

(defun register-online-help (names doc)
  (unless doc (return-from register-online-help nil))
  (cond ((stringp doc)
	 (dolist (name names)
	   (dolist (key (make-doc-key-from-string name))
	     (setf (gethash key *cafeobj-doc-db*) (make-oldoc :key key
							      :doc-string doc
							      :names name)))))
	(t (dolist (a-doc doc)
	     (let ((key-parts (butlast a-doc))
		   (doc-string (car (last a-doc))))
	       (dolist (keyp key-parts)
		 (dolist (key (make-doc-key-from-string keyp))
		   (setf (gethash key *cafeobj-doc-db*) (make-oldoc :key key
								    :doc-string doc-string
								    :names keyp)))))))))

(defparameter .md-remove-hash-hash. #~s/##//)
(defparameter .md-remove-link. #~s/{#.*}//)
(defparameter .md-remove-link2. #~s/\(#.+\)//)
(defparameter .md-remove-code-sign. #~s/~~//)
(defparameter .md-cafeobj. #~s/_cafeobj/CafeOBJ/)
(defparameter .md-replace-tilde. #~s/~/*/)
(defparameter .md-replace-bq. #~s/`/'/)

(defun format-description (doc)
  (funcall .md-replace-bq.
	   (funcall .md-replace-tilde.
		    (funcall .md-cafeobj.
			     (funcall .md-remove-code-sign.
				      (funcall .md-remove-link2.
					       (funcall .md-remove-link.
							(funcall .md-remove-hash-hash. doc))))))))

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
				    (doc nil))
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
       (register-online-help ',keys ',doc)))

(defun print-comde-usage (com)
  (format t "~&[Usage] ~s, not yet" com))


;;;
;;; Export
;;; export document string to a file.
;;;
(defparameter .md-refman-title. "!refman")

(defvar .out-done. (make-hash-table :test #'equal))

(defun export-refman (&optional (output "manual/md/reference.md"))
  (clrhash .out-done.)
  (let (doc keys)
    (with-open-file (out output :direction :output :if-exists :supersede :if-does-not-exist :create)
      (maphash #'(lambda (k doc) (declare (ignore doc)) (push k keys)) *cafeobj-doc-db*)
      (setq keys (remove .md-refman-title. keys :test #'string=))
      (setq keys (sort keys #'string<=))
      (push .md-refman-title. keys)
      (dolist (key keys)
	(setq doc (get-document-string key t))
	(unless doc
	  (error "The document string not found for ~s." key))
	(unless (gethash key .out-done.)
	  (format out "~a" doc)
	  (setf (gethash key .out-done.) t))))))

;;; EOF

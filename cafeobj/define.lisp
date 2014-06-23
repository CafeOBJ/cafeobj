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
				    (related nil)
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
       (register-online-help (car ',keys) (cdr ',keys) ',title ',mdkey ',doc ',example ',related)))

(defun print-comde-usage (com)
  (format t "~&[Usage] ~s, not yet" com))


;;; EOF

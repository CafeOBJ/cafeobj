;;;-*- Mode:LISP; Package: Chaos; Base:10; Syntax:Common-lisp -*-
;;; $Id: find.lisp,v 1.5 2010-07-15 04:40:55 sawada Exp $
(in-package :chaos)
#|==============================================================================
				 System: Chaos
			       Module: primitives
				File: find.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; ***********
;;; FIND MODULE
;;; ***********

(defun find-module-or-error (modexp)
  (declare (type (or module modexp) modexp))
  (when (%is-modexp modexp)
    (setq modexp (%modexp-value modexp)))
  (when (and (consp modexp) (null (cdr modexp)) (stringp (car modexp)))
    (setq modexp (car modexp)))
  (when (and (equal modexp "*the-current-module*")
	     *current-module*)
    (setq modexp *current-module*))
  (if (module-p modexp)
      modexp
      (let ((canon-name (canonicalize-simple-module-name modexp))
	    (mod nil))
	(declare (type (or simple-string list) canon-name))
	(if (stringp canon-name)
	    (let ((pos (position #\. (the simple-string canon-name) :from-end t)))
	      (if pos
		  (let ((name (subseq canon-name 0 pos))
			(qual (subseq canon-name (1+ pos)))
			(context nil))
		    (setf context (find-module-or-error qual))
		    (if (or (null context) (modexp-is-error context))
			(with-output-chaos-error ('no-such-module)
			  (format t "Could not evaluate modexpr ~a, " canon-name)
			  (format t " no such module ~a" qual)
			  )
			(setf mod (find-module-in-env name context))))
		  (setq mod (find-module-in-env canon-name))
		  )
	      (if mod
		  mod
		  (cons :error canon-name)))
	    (cons :error canon-name)))))

;;; *************************
;;; GETTING MODULE CONSTRUCTS___________________________________________________
;;; *************************

;;; FINDING MODULE'S SORTS _____________________________________________________
;;;
;;; SORT-NAME-IS-AMBIGUOUS : Name Module -> Bool
;;;
(defun sort-name-is-ambiguous (name module)
  (let ((flg nil))
    (dolist (s (append (module-error-sorts module)
		       (module-all-sorts module)))
      (if (eq name (sort-id s))
	  (if flg
	      (return-from sort-name-is-ambiguous t)
	      (setq flg t))))))

(defun sort-is-ambiguous (sort module)
  (sort-name-is-ambiguous (sort-id sort) module))

;;; FIND-SORTS-IN-MODULE

(defun find-sorts-in-module (sort-name &optional (module (or *current-module*
							     *last-module*)))
  (declare (type symbol sort-name)
	   (type module module))
  (let ((res nil))
    (dolist (s (module-all-sorts module) res)
      (if (eq sort-name (sort-id s))
	  (push s res)))))

;;; FIND-SORT 
;;; 
#||
(defun find-sort (sort-name-or-name-ref &optional (module (or *current-module*
							      *last-module*)))
  (unless module
    (error "Internal error,module is not specified: find-sort"))
  (unless (module-p module)
    (error "Internal error, find-sort: invalid module ~A" module))
  (let ((sort (get-sort-named sort-name-or-name-ref module)))
    (if sort sort
	(let ((ambig-sorts (find-sorts-in-module sort-name-or-name-ref module)))
	  (cond ((= (length ambig-sorts) 1) (car ambig-sorts))
		((> (length ambig-sorts) 1)
		 (with-output-chaos-warning ()
		   (princ "sort name ")
		   (princ sort-name-or-name-ref)
		   (princ " is ambiguous, arbitrary take ")
		   (print-chaos-object (setf sort (car (nreverse ambig-sorts))))
		   (princ " as the resolved name.")
		   )
		 sort)
		(t (or (get-sort-named sort-name-or-name-ref '*chaos-module*)
		       (with-output-chaos-warning ()
			 (princ "no such sort ")
			 (princ sort-name-or-name-ref)
			 nil))))))))

||#

;;; FIND-SORT-IN : Module Sort-Name -> Sort
;;; 
;;;  Sort-Name must be either
;;;   1) string : "FOO", "FOO.ModuleQualifier", 'Foo, 'FOO.ModuleQualifier
;;;   2) list   : '( "FOO" "ModuleQualifier") '('Foo "ModuleQualifier")
;;;   3) sort-ref : (%sort-ref "FOO" "ModuleQualifier")
;;;
(defun check-qualified-sort-name (sn)
  (declare (type t sn))
  (cond ((%is-sort-ref sn)
	 (let ((sort-name (%sort-ref-name sn))
	       (context (%sort-ref-qualifier sn)))
	   (if context
	       (values sort-name context)
	       (check-qualified-sort-name sort-name))))
	((symbolp sn) (check-qualified-sort-name (string sn)))
	((stringp sn)
	 (let ((pos (position #\. (the simple-string sn))))
	   (declare (type (or null fixnum) pos))
	   (if pos
	       (values (subseq (the simple-string sn) 0 pos)
		       (subseq (the simple-string sn) (1+ pos)))
	       (values sn nil))))
	((sort-struct-p sn)
	 (check-qualified-sort-name (sort-id sn)))
	((and (consp sn) (null (cdr sn)))
	 (check-qualified-sort-name (car sn)))
	((and (consp sn) (cdr sn))
	 (values (car sn) (cadr sn)))
	(t nil)))

(defun find-qual-sort (sort-name &optional (module *current-module*))
  (find-sort-in module sort-name))

(defparameter *universal-sort-names* '(|*Universal*| |*HUniversal*|))

(defun find-sort-in (module sort-name &optional search-in-mod)
  (declare (type module module)
	   (type (or sort* symbol string list) sort-name)
	   (values (or null sort*)))
  (cond ((sort-struct-p sort-name)
	 (if search-in-mod
	     (if (or (memq sort-name (module-all-sorts module))
		     (memq sort-name (module-error-sorts module)))
		 (return-from find-sort-in sort-name)
	       (return-from find-sort-in nil))
	   ;; else
	   (return-from find-sort-in sort-name)))
	(t (multiple-value-bind (sort-id mod-qual)
	       (check-qualified-sort-name sort-name)
	     (declare (type (or simple-string symbol) sort-id)
		      (type (or null modexp) mod-qual))
	     (let ((ss-name (string sort-id)))
	       (when (and mod-qual (eql #\? (schar ss-name 0)))
		 (let ((ssort (if (equal mod-qual (module-name module))
				  (find-sort-in module (subseq ss-name 1))
				(let ((cmod (find-module-in-env-ext
					     mod-qual module)))
				  (if cmod
				      (find-sort-in cmod (subseq ss-name 1))
				    nil)))))
		   (when ssort
		     (return-from find-sort-in
		       (the-err-sort ssort (module-sort-order module))))
		   )))
	     (when (stringp sort-id)
	       (setf sort-id (intern sort-id)))
	     (when (and (not mod-qual)
			t)		;  *allow-universal-sort*
	       (case sort-id
		 ($name-universal
		  (return-from find-sort-in *universal-sort*))
		 ($name-huniversal
		  (return-from find-sort-in *huniversal-sort*))
		 ($name-cosmos
		  (return-from find-sort-in *cosmos*))
		 (otherwise		; do nothing
		  nil)))
	     ;;
	     (if mod-qual
		 ;; qualified sort name
		 (if (equal mod-qual (module-name module))
		     (find-sort-in module sort-id)
		   (let ((cmod (find-module-in-env-ext mod-qual module)))
		     (if cmod
			 (find-sort-in cmod sort-id)
		       nil)))
	       ;; else
	       (let ((am nil))
		 (dolist (s (module-all-sorts module))
		   (when (eq sort-id (sort-id s))
		     (push s am)))
		 (if (cdr am)
		     (progn
		       (with-output-chaos-warning ()
			 (princ "in module ")
			 (print-chaos-object module)
			 (format t ", sort name ~a is ambiguous:"
				 (string sort-id))
			 (setq am (reverse am))
			 (dotimes (x (length am))
			   (format t "~&(~d) " (1+ x))
			   (print-chaos-object (nth x am))
			   (when *on-debug*
			     (let ((*print-array* nil)
				   (*print-circle* nil))
			       (print-next)
			       (format t "sort   = ~a" (nth x am))
			       (print-next)
			       (format t "module = ~a" (sort-module (nth x am)))
			       )))
			 (print-next)
			 (princ "arbitrary take ")
			 (print-chaos-object (car am))
			 (princ " as the resolved name."))
		       ;; (break)
		       (car (nreverse am)))
		   ;; else
		   (if am
		       (car am)
		     ;; else
		     (find-error-sort-in module sort-id)))))))
	))

(defun find-error-sort-in (module sort-name)
  (declare (type module module)
	   (type (or simple-string symbol) sort-name))
  (let ((err-sort-name (string sort-name))
	(sort nil))
    (if (eql #\? (schar err-sort-name 0))
	(let ((sub-sort-name (subseq err-sort-name 1)))
	  (dolist (sn (parse-with-delimiter sub-sort-name #\+))
	    ;; FIX ME this is not complete
	    (setq sort
	      (find-sort-in module sn))
	    (when sort (return)))
	  (if sort
	      (the-err-sort sort (module-sort-order module))))
      nil
      )))
	  

(defun find-all-sorts-in (module sort-name)
  (declare (type module module)
	   (type (or sort* symbol string list) sort-name))
  (when (sort-struct-p sort-name)
    (return-from find-all-sorts-in (list sort-name)))
  (multiple-value-bind (sort-id mod-qual)
      (check-qualified-sort-name sort-name)
    (declare (type (or simple-string symbol) sort-id)
	     (type (or null modexp) mod-qual))
    (when (stringp sort-id)
      (setf sort-id (intern sort-id)))
    (let ((res nil))
      (if mod-qual
	  (if (equal mod-qual (module-name module))
	      (setq res (find-sort-in module sort-id))
	      (let ((cmod (find-module-in-env-ext mod-qual module)))
		(setq res (find-sort-in cmod sort-id))))
	  (progn
	    (dolist (s (module-all-sorts module))
	      (when (eq sort-id (sort-id s))
		(push s res)))
	    (unless res
	      (setq res (find-error-sort-in module sort-id)))))
      (when (and res (atom res))
	(setq res (list res)))
      res)))

;;; FIND-SORT-IN-KEEP
;;;
(defun find-sort-in-keep (module sort)
  (declare (type module module)
	   (type sort* sort))
  (if (member sort (module-sorts module) :test #'eq)
      sort
      (find-sort-in module (sort-id sort))))

(defun find-sorts-in-keep (module sort-list)
  (declare (type module module)
	   (type list sort-list))
  (mapcar #'(lambda (s) (find-sort-in-keep module s)) sort-list) )

(defun simple-find-sort-in-local (module sort-id)
  (declare (type module module)
	   (type symbol sort-id))
  (dolist (sort (module-sorts module))
    (when (eq sort-id (sort-id sort))
      (return-from simple-find-sort-in-local sort))))

;;; *ASSUMPTION* error-sorts are generated.
;;;
(defun find-module-error-sorts (module)
  (declare (type module module))
  (let ((error-sorts nil)
	(so (module-sort-order module)))
    (declare (type sort-order so))
    (dolist (s (module-all-sorts module))
      (declare (type sort* s))
      (unless (memq (sort-module s) *kernel-hard-wired-builtin-modules*)
	(let ((es (the-err-sort s so)))
	  (when (err-sort-p es)
	    (pushnew es error-sorts)))))
    error-sorts))

(defun get-module-top-sorts (module)
  (declare (type module module))
  (let ((res nil)
	(sorts (module-all-sorts module)))
    (dolist (sort (maximal-sorts sorts (module-sort-order module)))
      (declare (type sort* sort))
      (when (not (or (err-sort-p sort)
		     (memq (sort-module sort)
			   *kernel-hard-wired-builtin-modules*)))
	(push sort res)))
    res))

;;; FINDING OPERATOR/MEHTOD ____________________________________________________
;;;

(defun operator-name-is-ambiguous (symbol module)
  (declare (type (or symbol list) symbol)
	   (type module module))
  (when (atom symbol) (setq symbol (list symbol)))
  (let ((num 0))
    (declare (type fixnum num))
    (dolist (opinfo (module-all-operators module))
      (when (equal symbol (operator-symbol (opinfo-operator opinfo)))
	(incf num)))
    (if (< 1 num)
	t
	nil)))

(defun filter-ops-with-type (opinfos type)
  (declare (type list opinfos)
	   (type symbol type))
  (let ((res nil))
    (dolist (opinfo opinfos)
      (let ((meth0 (car (opinfo-methods opinfo))))
	(case type
	  (:functional
	   (unless (method-is-behavioural meth0)
	     (push opinfo res)))
	  (t (when (method-is-behavioural meth0)
	       (push opinfo res))))))
    (nreverse res)))

;;; *NOTE* not used now.....
#|
(defun simple-find-operator (operator-symbol num-args module-id)
  (if (module-p module-id)
      (setf module-id (module-name module-id)))
  (get-operator-unique (list operator-symbol module-id) num-args))
|#

(defun match-op-symbol (sym1 sym2)
  (let ((s1 sym1)
	(s2 sym2))
    (loop
	(unless s2
	  (return-from match-op-symbol nil))
	(unless (equal (car s1) (car s2))
	  (if (equal (car s2) "_")
	      (return-from match-op-symbol
		(match-op-symbol s1 (cdr s2)))
	      (return-from match-op-symbol nil)))
      (setf s1 (cdr s1)
	    s2 (cdr s2))
      (unless s1 (return-from match-op-symbol t))
      )))

;;; FIND-OPERATORS-IN-MODULE
;;;   : operator-symbol number-of-arguments module -> List[OpInfo]
;;; operator-symbol must of a string or list of string (token seq).
;;;
(defun find-operators-in-module (operator-symbol num-args module
						 &optional
						 type
						 allow-match)
  (declare (type (or symbol string list) operator-symbol)
	   (type fixnum num-args)
	   (type (or module modexp) module)
	   (type symbol type))
  (when (atom operator-symbol) (setf operator-symbol (list operator-symbol)))
  (let ((mod (if (module-p module)
		 module
		 (find-module-in-env-ext module)))
	(name (cons operator-symbol num-args))
	(res nil))
    (unless mod (error "Panic! no such module ~s" module))
    (dolist (opinfo (module-all-operators (the module mod)))
      (if allow-match
	  (when (match-op-symbol name
				 (operator-name (opinfo-operator opinfo)))
	    (push opinfo res))
	  (when (equal name (operator-name (opinfo-operator opinfo)))
	    (push opinfo res))))
    ;;
    (when type
      (setq res (filter-ops-with-type res type)))
    res))

;;; FIND-OPERATORS-IN-MODULE-NO-NUMBER : operator-symbol module -> List[OpInfo]
;;; operator-symbol must be a string or list of string (tokens).
;;;
(defun find-operators-in-module-no-number (operator-symbol module
							   &optional
							   type
							   allow-match)
  (when (atom operator-symbol) (setf operator-symbol (list operator-symbol)))
  (let ((mod (if (module-p module) module
		 (find-module-in-env-ext module)))
	(res nil))
    (unless mod (error "Panic! no such module ~s" module))
    (dolist (opinfo (module-all-operators mod) res)
      (if allow-match
	  (when (match-op-symbol operator-symbol
				 (operator-symbol (opinfo-operator opinfo)))
	    (push opinfo res))
	  (when (equal operator-symbol (operator-symbol
					(opinfo-operator opinfo)))
	    (push opinfo res)))
      )
    ;;
    (when type
      (setq res (filter-ops-with-type res type)))
    res))

;;; FIND-OPERATOR : name number-of-arguments module -> OpInfo
;;;
(defun find-operator (op-name &optional
			      (num-args nil)
			      (module nil)
			      (type nil))
  (declare (type (or symbol list) op-name)
	   (type (or null fixnum) num-args)
	   (type symbol type))
  (if num-args
      (let ((opinfos (find-operators-in-module op-name num-args module type)))
	(unless (cdr opinfos)
	  (return-from find-operator (car opinfos)))
	(with-output-chaos-warning ()
	  (format t "operator name ~a is ambiguous," op-name)
	  (print-next)
	  (princ "qualify it by module name or sort-name"))
	nil)
      (let ((opinfos (find-operators-in-module-no-number op-name module type)))
	(if (cdr opinfos)
	    (progn
	      (with-output-chaos-warning ()
		(format t "operator name ~a is ambiguous," op-name)
		(print-next)
		(princ " specify the number of arguments or qualify it."))
	      (return-from find-operator nil))
	    (car opinfos)))))

;;; 
(defun implode-op-ref (name)
  (declare (type list name))
  (let ((num nil)
	(op-id nil))
    (cond ((cdr name)
	   (cond ((equal "/" (nth (- (length name) 2) name))
		  (setf num (parse-integer (car (last name)) :junk-allowed t))
		  (if (and (integerp num) (<= 0 (the fixnum num)))
		      (setf op-id
			    (butlast (butlast name))
			    )
		      (progn (setf op-id name)
			     (setf num nil)
			     (when (member "_" name :test #'equal)
			       (setf num 0)
			       (dolist (n name)
				 (if (equal n "_")
				     (incf (the fixnum num) 1)))))))
		 (t (let ((pos (position #\/ (the simple-string (car (last name)))
					 :from-end t)))
		      (if pos
			  (progn
			    (setf num (parse-integer (subseq (the simple-string
							       (car (last name)))
							     (1+ pos))
						     :junk-allowed t))
			    (if (and (integerp num) (<= 0 (the fixnum num)))
				(setf op-id
				      (append (butlast name)
					      (subseq (the simple-string
							(car (last name)))
						      0 pos)))
			        (progn
				  (setf op-id name)
				  (setf num nil)
				  (when (member "_" name :test #'equal)
				    (setf num 0)
				    (dolist (n name)
				      (if (equal n "_")
					  (incf (the fixnum num) 1)))))))
			  (progn
			    (setf op-id name)
			    (setf num nil)
			    (when (member "_" name :test #'equal)
			      (setf num 0)
			      (dolist (n name)
				(if (equal n "_")
				    (incf (the fixnum num) 1))))))))))
	  (t (let ((pos (position #\/
				  (the simple-string
				    (car name))
				  :from-end t)))
	       (if pos
		   (progn
		     (setf num (parse-integer (subseq (the simple-string (car name))
						      (1+ pos))
					      :junk-allowed t))
		     (if (and (integerp num) (<= 0 (the fixnum num)))
			 (setf op-id
			       (list (subseq (the simple-string (car name))
					     0 pos)))
			 (progn
			   (setf op-id name)
			   (setf num nil))))
		 (progn
		   (setf num nil)
		   (setf op-id name))
		 ))))
    (values op-id num)))

;;; FIND-QUAL-OPERATOR-IN : module name number-of-arguments -> { OpInfo | nil }
;;; the standard operation for resolving operator references.
;;;
(defun find-qual-operator-in (module name &optional num-args type)
  (declare (type module module)
	   (type list name)
	   (type (or null fixnum) num-args)
	   (type symbol type))
  (unless num-args
     (multiple-value-bind (nam n-args)
	 (implode-op-ref name)
       (if (and nam n-args)
	   (setf name nam
		 num-args n-args))))
  (find-operator name num-args module type))

;;; FIND-ALL-QUAL-OPERATORS-IN : module name number-of-args -> List[OpInfo]
;;;
(defun find-all-qual-operators-in (module name &optional num-args type)
  (declare (type module module)
	   (type list name)
	   (type (or null fixnum) num-args)
	   (type symbol type))
  (unless num-args
     (multiple-value-bind (nam n-args)
         (implode-op-ref name)
       (if (and nam n-args)
	   (setf name nam
		 num-args n-args))))
  (if num-args
      (find-operators-in-module name num-args module type)
      (find-operators-in-module-no-number name module type)))

;;; FIND-OPERATORS-NUM-ARGS module num-args : -> List[OpInfo]
;;;
(defun find-operators-num-args (module num-args &optional type)
  (declare (type module module)
	   (type fixnum num-args)
	   (type symbol type))
  (let ((res nil))
    (dolist (opinfo (module-all-operators module))
      (if (= num-args (the fixnum (operator-num-args (opinfo-operator opinfo))))
	  (push opinfo res)))
    (when type
      (setq res (filter-ops-with-type res type)))
    ;;
    (nreverse res)))

;;; FIND-METHOD-IN : module name arity coarity -> Method
;;; within a given module the "name" arity and coarity of an operator
;;; uniquely identify the method.
;;;
(defun find-method-in (module op-name arity coarity)
  (declare (type module module)
	   (type list arity)
	   (type (or list string) op-name)
	   (type sort* coarity))
  (let ((len (length arity)))
    (declare (type fixnum len))
    (dolist (opinfo (find-operators-in-module op-name len module) nil)
      (dolist (meth (opinfo-methods opinfo))
	(if (and (sort= coarity (method-coarity meth))
		 (= len (the fixnum (length (method-arity meth))))
		 (every #'(lambda (x y) (sort= x y))
			arity (method-arity meth)))
	    (return-from find-method-in meth))))))

;;; FIND-BUILTIN-METHOD-IN module sort op-name
;;;
(defun find-builtin-method-in (module sort op-name)
  (declare (type module module)
	   (type sort* sort)
	   (type t op-name))
  (if (null (cdr op-name))
      (let ((sort-info (bsort-info sort)))
	(when sort-info
	  (let ((opnm (car op-name)))
	    (if (funcall (car sort-info) opnm) ; token predicate
		(make-bconst-term sort opnm)
		(with-in-module (module)
		  (let ((srt nil))
		    (dolist (x (subsorts sort))
		      (let ((si nil))
			(when (and (sort-is-builtin sort)
				   (setf si (bsort-info sort))
				   (or (null srt)
				       (sort< x srt))
				   (funcall (car si) opnm))
			  (setq srt x))))
		    (if srt
			(make-bconst-term srt opnm)
			nil)
		    ))))))
      nil))
			
;;; FIND-METHOD-NAMED-IN (module op-symbol)
;;;
(defun find-method-named-in (module op-symbol)
  (declare (type module module)
	   (type list op-symbol))
  (let ((opinfos (find-operators-in-module-no-number op-symbol module)))
    (if opinfos
	(car (opinfo-methods (car opinfos)))
	;;
	(dolist (srt (module-all-sorts module) nil)
	  (if (sort-is-builtin srt)
	      (let ((res (find-builtin-method-in module srt op-symbol)))
		(if res (return res))))))))
	  
;;; FIND-ALL-MEHTODS-NAMED-IN
;;;
(defun find-all-methods-named-in (module op-name)
  (declare (type module module)
	   (type list op-name))
  (nconc (let ((opinfos (find-operators-in-module-no-number op-name module))
	       (res nil))
	   (dolist (info opinfos)
	     (setf res (append res (opinfo-methods info))))
	   res)
	 (mapcan #'(lambda (srt)
		     (if (sort-is-builtin srt)
			 (let ((res (find-builtin-method-in module srt op-name)))
			   (if res (list res)))))
		 (module-all-sorts module))))
      
;;; FIND-ALL-MEHTODS-NAMED-IN-SORT module op-name sort
;;;
(defun find-all-methods-named-in-sort (module op-name sort)
  (declare (type module module)
	   (type list op-name)
	   (type sort* sort))
  (let ((so (module-sort-order module)))
    (declare (type sort-order so))
    (append (let ((opinfos (find-operators-in-module-no-number op-name module))
		  (res nil))
	      (dolist (info opinfos)
		(let ((res1 (find-if
			     #'(lambda (method)
				 (sort<= (method-coarity method) sort so))
			     (opinfo-methods info))))
		  (if res1
		      (setf res (nconc res res1)))))
	      res)
	    (mapcan #'(lambda (srt)
			(if (and (sort-is-builtin srt)
				 (sort<= srt sort so))
			    (let ((res (find-builtin-method-in module srt op-name)))
			      (if res (list res)))))
		    (module-all-sorts module)))))

(defun find-error-method-in (module method)
  (declare (type module module)
	   (type method method))
  (when (memq (method-module method)
	      *kernel-hard-wired-builtin-modules*)
    (return-from find-error-method-in method))
  (when (method-is-universal method)
    (return-from find-error-method-in method))
  ;;
  (or (car (memq method (module-error-methods module)))
      (let* ((alen (length (method-arity method)))
	     (opinfos (find-operators-in-module (method-symbol method)
						alen
						module))
	     (so (module-sort-order module)))
	;;
	(unless opinfos
	  (with-output-panic-message ()
	    (princ "finding error method, could not find opinfo! : ")
	    (print-chaos-object method)
	    (chaos-error 'panic)))
	;;
	(let (;; (opinfo nil)
	      (err-method nil))
	  (unless 
	      (block find-method
		(let* ((ar (mapcar #'(lambda (x)
				       (if (err-sort-p x)
					   (find-compatible-err-sort x module nil)
					   (the-err-sort x so)))
				   (method-arity method)))
		       (ar-names (mapcar #'(lambda(x) (sort-id x))
					 ar))
		       (cr (if (err-sort-p (method-coarity method))
			       (find-compatible-err-sort (method-coarity method)
							 module
							 nil)
			       (the-err-sort (method-coarity method) so)))
		       (cr-name (sort-id cr)))
		  (dolist (oi opinfos)
		    (dolist (cand (opinfo-methods oi))
		      (when (and (equal ar-names
					(mapcar #'(lambda (x) (sort-id x))
						(method-arity cand)))
				 (equal cr-name
					(sort-id (method-coarity cand))))
			;; (setq opinfo oi)
			(setq err-method cand)
			(return-from find-method t))
		      ))))
	    #||
	    (with-output-panic-message ()
	    (princ "could not find error operator! : ")
	    (print-chaos-object method)
	    (chaos-error 'panic))
	    ||#
	    (return-from find-error-method-in method))
	  ;;
	  err-method))))

;;; VARIABLES ------------------------------------------------------------------

;;; FIND-VARIABLE-IN
;;;
(defun find-variable-in (module variable-name)
  (declare (type module module))
  (when (stringp variable-name) (setq variable-name (intern variable-name)))
  (cdr (find variable-name (module-variables module)
	     :key 'car
	     :test #'(lambda (n v) (eq n v))))
  )

;;; PARAMETERS -----------------------------------------------------------------

(defun get-module-imported-parameters (module)
  (declare (type module))
  (let ((res (cons nil nil)))
    (get-module-imported-parameters* module res)
    (cdr res)))

#||
(defun get-module-imported-parameters* (module res)
  (declare (type module module)
	   (type list res))
  (when (or (module-is-inconsistent module)
	    (null (module-name module)))
    (return-from get-module-imported-parameters* nil))
  (dolist (param (module-parameters module))
    (pushnew param (cdr res) :test #'equal))
  (dolist (impsub (module-direct-submodules module))
    (unless (eq :using (cdr impsub))
      (let* ((sub (car impsub))
	     (sub-name (module-name sub)))
	(cond ((or (%is-instantiation sub-name)
		   (int-instantiation-p sub-name))
	       (let ((args nil)
		     (ins-mod nil))
		 (if (%is-instantiation sub-name)
		     (progn
		       (setq args (%instantiation-args sub-name))
		       (setq ins-mod (%instantiation-module sub-name)))
		     (progn
		       (setq args (int-instantiation-args sub-name))
		       (setq ins-mod (int-instantiation-module sub-name))))
		 (dolist (is (module-direct-submodules sub))
		   (let ((is-mod (car is))
			 (rst nil))
		     (if (module-is-parameter-theory is-mod)
			 (when (member (setq rst
					     (parameter-theory-arg-name is-mod))
				       args
				       :test #'(lambda (a arg)
						 (let ((arg-name
							(%!arg-name arg))
						       (arg-view
							(%!arg-view arg)))
						   (or
						    (equal arg-view "DUMMY")
						    (progn
						      (when (numberp arg-name)
							(setq arg-name
							      (get-module-nth-arg-name
							       ins-mod
							       arg-name)))
						      (when (and (consp arg-name)
								 (null (cdr arg-name)))
							(setq arg-name (car arg-name)))
						      (not (equal a arg-name))))))
					 )
			   (pushnew (cons (cons rst is-mod)
					  (cdr is))
				    (cdr res)
				    :test #'equal))
			 ;;
			 (get-module-imported-parameters* is-mod res)
			 ))))
	       )
	      ((modexp-is-parameter-theory sub-name)
	       (pushnew (cons (cons (car sub-name)
				    sub)
			      (cdr impsub))
			(cdr res)
			:test #'equal))
	      (t
	       (get-module-imported-parameters* sub res)
	       ))))
    ))

||#

(defun get-module-imported-parameters* (module res)
  (declare (type module module)
	   (type list res))
  (unless (module-p module)
    (return-from get-module-imported-parameters* nil))
  ;;
  (when (or (module-is-inconsistent module)
	    (null (module-name module)))
    (return-from get-module-imported-parameters* nil))
  (dolist (param (module-parameters module))
    (pushnew param (cdr res) :test #'equal))
  (dolist (impsub (module-direct-submodules module))
    (unless (eq :using (cdr impsub))
      (let* ((sub (car impsub))
	     (sub-name (module-name sub)))
	(cond ((module-is-parameter-theory sub)
	       (pushnew (cons (cons (parameter-theory-arg-name sub)
				    sub)
			      (cdr impsub))
			(cdr res)
			:test #'equal))
	      ((or (%is-instantiation sub-name)
		   (int-instantiation-p sub-name))
	       (let ((args nil)
		     (ins-mod nil))
		 (if (%is-instantiation sub-name)
		     (progn
		       (setq args (%instantiation-args sub-name))
		       (setq ins-mod (%instantiation-module sub-name)))
		     (progn
		       (setq args (int-instantiation-args sub-name))
		       (setq ins-mod (int-instantiation-module sub-name))))
		 (dolist (is (module-direct-submodules sub))
		   (let ((is-mod (car is))
			 (rst nil))
		     (if (module-is-parameter-theory is-mod)
			 (when (member (setq rst
					     (parameter-theory-arg-name is-mod))
				       args
				       :test #'(lambda (a arg)
						 (let ((arg-name
							(%!arg-name arg))
						       (arg-view
							(%!arg-view arg)))
						   (or
						    (equal arg-view "DUMMY")
						    (progn
						      (when (numberp arg-name)
							(setq arg-name
							      (get-module-nth-arg-name
							       ins-mod
							       arg-name)))
						      (when (and (consp arg-name)
								 (null (cdr arg-name)))
							(setq arg-name (car arg-name)))
						      (not (equal a arg-name))))))
					 )
			   (pushnew (cons (cons rst is-mod)
					  (cdr is))
				    (cdr res)
				    :test #'equal))
			 ;;
			 (get-module-imported-parameters* is-mod res)
			 ))))
	       )
	      ((%is-rename sub-name)
	       (get-module-imported-parameters* (%rename-module sub-name)
						res))
	      ((int-rename-p sub-name)
	       (get-module-imported-parameters* (int-rename-module sub-name)
						res))
	      (t
	       (get-module-imported-parameters* sub res)
	       ))))
    ))

(defun get-module-parameters (module)
  (declare (type module module))
  (get-module-imported-parameters module))

;;; FIND-PARAMETERIZED-SUBMODULE
;;;
(defun find-parameterized-submodule (name module)
  (declare (type (or fixnum modexp) name)
	   (type (or module modexp) module))
  (unless (module-p module)
    (setq module (eval-modexp module))
    (when (or (modexp-is-error module)
	      (null module))
      (with-output-panic-message ()
	(format t "Internal error, could not evaluate modexp ~a" module)
	(chaos-error 'panic))))
  (let ((params (get-module-parameters module)))
    (cond ((integerp name)
	   (when (< name 0)
	     (with-output-chaos-error ('invalid-parameter-number)
	       (princ "parameter number must be more than or equal to 1")
	       ))
	   (let ((param (nth name params)))
	     (if param
		 (parameter-theory-module param)
		 nil)))
	  ((consp name)
	   (let ((real-name (car name))
		 (context (cdr name)))
	     (unless (or (module-p context) (null context))
	       (with-output-chaos-error ('no-context)
		 (princ "context for parameter name must be evaluated : " )
		 (print-chaos-object context)
		 ))
	     (find-parameterized-submodule real-name (if context
							 context
							 module))))
	  ((stringp name)
	   (let ((param (find-if #'(lambda (x)
				     (equal name (parameter-arg-name x)))
				 params)))
	     (if param
		 (parameter-theory-module param)
		 (progn
		   (setq param (find-module-in-env-ext name module))
		   (if (module-is-parameter-theory param)
		       param
		       (cons :error name))))))
	  (t (with-output-panic-message ()
	       (princ "invalid parameter name comes : ")
	       (print-chaos-object name)
	       (chaos-to-top))))))

(defun get-module-nth-arg-name (mod num)
  (declare (type (or module modexp) mod)
	   (type fixnum num))
  (if (module-p mod)
      (let ((param (nth num (get-module-parameters mod))))
	(if param
	    (parameter-arg-name param)
	    nil))
      (let ((mod (find-module-in-env (normalize-modexp mod))))
	(when mod
	  (get-module-nth-arg-name mod num)))))


;;; SUBMODULE -------------------------------------------------------------------
(defun nth-sub (no mod)
  (declare (type t no)
	   (type module mod))
  (unless (integerp no)
    (with-output-chaos-error ('invalid-submodule-number)
      (format t "Invalid submodule number ~a" no)
      ))
  (unless (>= (the fixnum no) 0)
    (with-output-chaos-error ('invalid-submodule-number)
      (princ "submodule number must be greater than or equal to 1.")
      ))
  (let ((lst nil)
	(params (module-parameters mod)))
    (dolist (i (module-submodules mod))
      (when (not (rassoc (car i) params)) (push (car i) lst)))
    (nth (the fixnum no) lst)
    ))

;;; AXIOMS _____________________________________________________________________

;;; will be set by prelude/prelude.lisp
(defvar *apply-ignore-modules* nil)

(defun module-own-axioms (mod &optional no-system-axiom)
  (declare (type module mod)
	   (type (or null t) no-system-axiom))
  (if no-system-axiom
      (nconc (remove-if-not #'(lambda (x)
				(declare (type axiom x))
				(or (null (axiom-kind x))
				    (eq :bad-rule (axiom-kind x))
				    (eq :bad-beh (axiom-kind x))))
			    (module-equations mod))
	     (module-rules mod))
      (append (module-equations mod) (module-rules mod))))

(defun module-own-axioms-ordered (mod &optional no-system-axiom)
  (declare (type module mod)
	   (type (or null t) no-system-axiom))
  (if no-system-axiom
      (nconc (nreverse (remove-if-not #'(lambda (x)
					  (declare (type axiom x))
					  (or (null (axiom-kind x))
					      (eq :bad-rule (axiom-kind x))
					      (eq :bad-beh (axiom-kind x))))
				      (module-equations mod)))
	     (reverse (module-rules mod)))
      (nconc (reverse (module-equations mod))
	     (reverse (module-rules mod)))))

(defvar *get-axioms-seen-mod* nil)

(defun module-imported-axioms (mod &optional no-system-axiom)
  (declare (type module mod)
	   (type (or null t) no-system-axiom))
  (setq *get-axioms-seen-mod* nil)
  (module-imported-axioms* mod no-system-axiom))

(defun module-imported-axioms* (mod no-system-axiom)
  (declare (type module mod)
	   (type (or null t) no-system-axiom))
  (let ((res nil)
	(subs (nreverse (module-direct-submodules mod))))
    (dolist (sub subs)
      (block next-sub
	(let ((sm (car sub)))
	  (when (memq sm *get-axioms-seen-mod*)
	    (return-from next-sub nil))
	  (push sm *get-axioms-seen-mod*)
	  (when (eq :using (cdr sub))
	    (return-from next-sub nil))
	  (when (memq sm *apply-ignore-modules*)
	    (return-from next-sub nil))
	  (let ((sub-ax nil)
		(to-be-fixed (module-axioms-to-be-fixed mod)))
	    (dolist (ax (module-own-axioms-ordered sm no-system-axiom))
	      (push (or (cdr (assq ax to-be-fixed))
			ax)
		    sub-ax))
	    (setq res
		  (nconc res
			 (nconc (nreverse sub-ax)
				(mapcar #'(lambda (x)
					    (or (cdr (assq x to-be-fixed))
						x))
					(module-imported-axioms*
					 sm no-system-axiom)))))
	    ))))
    ;;
    (delete-duplicates res :test #'eq)))

(defun get-module-axioms (mod &optional no-system-equations)
  (declare (type module mod)
	   (type (or null t) no-system-equations))
  (if (not (or *module-all-rules-every*
	       *chaos-verbose*
	       *print-all-eqns*))
      (module-own-axioms-ordered mod)
      (append (module-own-axioms-ordered mod)
	      (module-imported-axioms mod no-system-equations))))

;;; EOF




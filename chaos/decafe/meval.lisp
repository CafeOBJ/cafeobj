;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: meval.lisp,v 1.4 2010-06-17 08:23:18 sawada Exp $
(in-package :chaos)
#|==============================================================================
				 System: CHAOS
				 Module: deCafe
				File: meval.lisp
					
		     -- based on the implemetation of OBJ3.
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; == DESCRIPTION =============================================================
;;; EVALUATORS OF MDULE EXPRESSION INTERNAL FORMS
;;; *NOTE* As for views, see "view.lisp".

;;; ****
;;; EVAL________________________________________________________________________
;;; ****

;;; EVAL-MODEXP-TOP : modexp -> module
;;;
(defun eval-modexp-top (modexp &optional local-too)
  (clear-modexp-eval)
  ;; (eval-modexp (%modexp-value modexp))
  (eval-modexp modexp local-too))

(declaim (special *on-autoload*))
(defvar *on-autoload* nil)

;;; EVAL-MODEXP : modexp -> module
;;;
(defun eval-modexp+ (modexp)
  (let ((mod (eval-modexp modexp t nil)))
    (if (modexp-is-error mod)
	nil
      mod)))

(defun eval-modexp (modexp &optional also-local (reconstruct-if-need t))
  (declare (type t modexp))
  (when (module-p modexp)
    (return-from eval-modexp
      (if reconstruct-if-need
	  (reconstruct-module-if-need modexp)
	modexp)))
  (let ((mod nil)
	(me (normalize-modexp modexp)))
    (when (and (equal me "THE-LAST-MODULE")
	       *last-module*)
      (return-from eval-modexp
	(if reconstruct-if-need
	    (reconstruct-module-if-need *last-module*)
	  *last-module*)))
    (when (and (equal me ".")
	       *current-module*)
      (return-from eval-modexp
	*current-module*))
    (when (stringp me)
      (let ((pos (position #\. (the simple-string me) :from-end t)))
	(if pos
	    (let ((name (subseq (the simple-string me) 0 (the fixnum pos)))
		  (qual (subseq (the simple-string me) (1+ (the fixnum pos))))
		  (context nil))
	      ;; the context can itself be a local module
	      (setf context (eval-modexp qual t))
	      (if (modexp-is-error context)
		  (with-output-chaos-error ('no-such-module)
		    (format t "Could not evaluate modexpr ~a, " me)
		    (format t " no such module ~a" qual)
		    )
		(setf mod (find-module-in-env name context))))
	  (setq mod (find-module-in-env me (if also-local
					       *current-module*
					     nil))))))
    (if mod
	(if reconstruct-if-need
	    (reconstruct-module-if-need mod)
	  mod)
      ;; autoloading
      (let ((ent (assoc me *autoload-alist* :test #'equal)))
	(cond ((and ent (not (equal (car ent) *on-autoload*)))
	       (let ((*on-autoload* me))
		 (declare (special *on-autoload*))
		 (!input-file (cdr ent)))
	       (setq mod (find-module-in-env me (if also-local
						    *current-module*
						  nil)))
	       (if mod
		   mod
		 (cons :error me)))
	      (t (let ((newmod (eval-modexp* me)))
		   (if (modexp-is-error newmod)
		       newmod
		     (progn
		       (add-modexp-defn me newmod)
		       newmod)))))))))

;;; EVAL-MODEXP* : modexp -> module
;;; creates a module from a canonicalized module expression.
;;; 
;;; ** NOTE ** 
;;; the following SHOULD BE able to assume that component module expressions
;;; have already be evaluated in the process of canonicalization, i.e.,
;;; eval-modexp* instead of eval-modexp, how? 
;;;
(defun eval-modexp* (modexp)
  (cond ((stringp modexp)
	 (cons :error modexp))		; simple name at this point is always
					; treated as invalid modexp... can be
					; optimized though. 
	((modexp-is-parameter-theory modexp)
					; and also for (X "::" M)
	 (cons :error modexp))
	
	;; PLUS
	((or (%is-plus modexp) (int-plus-p modexp))
	 (compile-module (create-plus modexp) t))

	;; RENAME
	((or (%is-rename modexp) (int-rename-p modexp))
	 (compile-module (create-rename modexp) t))

	;; INSTANTIATION
	((or (%is-instantiation modexp) (int-instantiation-p modexp))
	 (compile-module (create-instantiation modexp) t))
	  
	;; VIEW
	((%is-view modexp) (complete-view modexp nil))
	  
	;; MODULE
	((module-p modexp)
	 (compile-module modexp))
	
	;; Internal Error!
	(t (with-output-chaos-error ('invalid-modexp)
	     (format t "bad modexp form ~s" modexp)))
	))

;;; ************************
;;; SPECIFIC MODULE CREATORS____________________________________________________
;;; ************************

;;; CREATE-RENAMED-MODULE : MODULE NAME -> MODULE
;;; creates a new module with name 'NAME' which is isomorphic to given module.
;;; structure of the module hierarchy of original module is preserved
;;  == just top-level rename only.
;;; ** used for construct local parameter theory.
;;; * TODO* how about module paramters?
(declaim (special *copy-variables*))
(defvar *copy-variables* nil)

#||
(defun create-renamed-module (mod name)
  (let ((*beh-proof-in-progress* t)
	(*copy-variables* t))
    (let ((newmod (eval-ast (%module-decl* (normalize-modexp name)
					   (module-kind mod)
					   :user
					   (list (%import* :using mod))))))
      (add-modexp-defn (module-name newmod) newmod)
      (compile-module newmod)
      newmod)
    ))
||#
(defun create-renamed-module (mod name)
  (let ((*beh-proof-in-progress* t)
	(*copy-variables* t)
	(*auto-context-change* nil))
    (let ((newmod (eval-ast (%module-decl* (normalize-modexp name)
					   (module-kind mod)
					   :user
					   nil))))
      (import-module newmod :using mod)
      (add-modexp-defn (module-name newmod) newmod)
      (compile-module newmod)
      newmod)
    ))

(defun create-renamed-module-2 (mod name context-module)
  (let ((*copy-variables* t)
	(*auto-context-change* nil))
    (let ((newmod (eval-ast (%module-decl* (normalize-modexp name)
					   (module-kind mod)
					   :user
					   nil))))
      (incorporate-module-copying newmod mod t nil context-module)
      (add-modexp-defn (module-name newmod) newmod)
      (compile-module newmod)
      newmod)
    ))

;;; ***********
;;; CREATE-PLUS : Modexp -> Module
;;; ***********
;;; a plus like an object that protects only of the components.
;;;
(defun create-plus (modexp)
  (flet ((report-error (&rest ignore)
	   (declare (ignore ignore))
	   (with-output-msg ()
	     (format t "could not evaluate plus: ")
	     (print-modexp modexp)
	     (chaos-error 'modexp-error))))
    (with-chaos-error (#'report-error)
      (cond ((int-plus-p modexp)	; evaluated internal rep.
	     (let ((newmod (create-module modexp)))
	       (with-in-module (newmod)
		 (dolist (mod (int-plus-args modexp))
		   (import-module-internal newmod :protecting mod))
		 (compile-module newmod))
	       newmod))
	    (t				; no yet evaluated, generate from the
					; scratch.
	     (let ((args (%plus-args modexp))
		   (res nil))
	       (dolist (arg args)
		 ;; arguments must not local module ..
		 (let ((val (eval-modexp arg nil)))
		   (when (modexp-is-error val)
		     (with-output-chaos-error ('modexp-eval)
		       (format t "could not evaluate an argument to `+' : ")
		       (print-modexp arg)
		       ))
		   (push val res)))
	       (let* ((name (make-int-plus :args res))
		      (newmod (or *modmorph-new-module* (create-module name))))
		 (setf (module-decl-form newmod) modexp)
		 (with-in-module (newmod)
		   (dolist (mod res)
		     (import-module-internal newmod :protecting mod))
		   (compile-module newmod)
		   newmod))))))))

;;; ********************
;;; CREATE-INSTANTIATION : MODEXP -> MODULE
;;; ********************
;;; *NOTE* apply-modmorph must use memo tables since mapping may affect
;;; sub-modules (e.g. with "protecting A[X <= Y]")
;;;
;;;
#||
(defun create-instantiation (modexp)
  (flet ((report-error (&rest ignore)
	   (declare (ignore ignore))
	   (with-output-msg ()
	     (princ "could not evaluate instantiation: ")
	     (print-modexp modexp *standard-output* t t)
	     (chaos-error 'modexp-error))))
    (with-chaos-error (#'report-error)
      (cond ((int-instantiation-p modexp) ; evaluated internal modexp.
	     (let ((mappg (views-to-modmorph (int-instantiation-module modexp)
					     (int-instantiation-args modexp))))
	       (apply-modmorph modexp mappg (int-instantiation-module modexp))))
	    (t				; not yet evaluated, build from the
					; scratch.
	     (let* ((*auto-context-change* nil)
		    ;; parameter module must be a global
		    (modpar (eval-modexp (%instantiation-module modexp))))
	       (unless (module-p modpar)
		 (with-output-chaos-error ('modexp-err)
		   (princ  "Unknown parameterized module in instantiation: ")
		   (when (modexp-is-error modpar)
		       (princ (cdr modpar))
		       ))
		 )
	       #||
	       (when (eq *current-module* modpar)
		 (with-output-chaos-error ('modexp-eval)
		   (princ "module ")
		   (print-mod-name *current-module*)
		   (princ "cannot instantiate itself")
  	         ))
	       ||#
	       (unless (get-module-parameters modpar)
		 (with-output-chaos-error ('modexp-eval)
		   (princ "module ")
		   (print-mod-name modpar)
		   (princ " has no parameters.")
		   ))
	       ;; 
	       (let ((args (do ((r (%instantiation-args modexp) (cdr r))
				(res nil))
			       ((null r) (nreverse res))
			     (push (eval-view-arg (car r)
						  modpar)
				   res))))
		 (let ((name (make-int-instantiation :module modpar
						     :args args))
		       (mappg (views-to-modmorph modpar args)))
		   (let ((module (apply-modmorph name mappg modpar)))
		     ;; (setf (module-name module) name) ; name is set by apply-modmorph.
		     (setf (module-decl-form module) modexp)
		     module)))))))))
||#

(defun create-instantiation (modexp)
  (flet ((report-error (&rest ignore)
	   (declare (ignore ignore))
	   (with-output-msg ()
	     (princ "could not evaluate instantiation: ")
	     (print-modexp modexp *standard-output* t t)
	     (chaos-error 'modexp-error))))
    (with-chaos-error (#'report-error)
      (cond ((int-instantiation-p modexp) ; evaluated internal modexp.
	     (let ((mappg (views-to-modmorph (int-instantiation-module modexp)
					     (int-instantiation-args modexp))))
	       (apply-modmorph modexp mappg (int-instantiation-module modexp))))
	    (t				; not yet evaluated, build from the
					; scratch.
	     (let* ((*auto-context-change* nil)
		    ;; parameter module must be a global
		    (modpar (eval-modexp (%instantiation-module modexp))))
	       (unless (module-p modpar)
		 (with-output-chaos-error ('modexp-err)
		   (princ  "Unknown parameterized module in instantiation: ")
		   (when (modexp-is-error modpar)
		       (princ (cdr modpar))
		       ))
		 )
	       (unless (get-module-parameters modpar)
		 (with-output-chaos-error ('modexp-eval)
		   (princ "module ")
		   (print-mod-name modpar)
		   (princ " has no parameters.")
		   ))
	       ;; 
	       (let ((args nil)
		     (mappg nil))
		 (push (eval-view-arg (car (%instantiation-args modexp))
				      modpar
				      nil)
		       args)
		 (setq mappg (view->modmorph modpar (car args)))
		 ;;
		 (dolist (r (cdr (%instantiation-args modexp)))
		   (push (eval-view-arg r modpar mappg) args)
		   (setq mappg
			 (modmorph-merge mappg
					 (view->modmorph modpar (car args)))))
		 (setq args (nreverse args))
		 ;;
		 (let ((name (make-int-instantiation :module modpar
						     :args args)))
		   (let ((module (apply-modmorph name mappg modpar)))
		     ;; (setf (module-name module) name) ; name is set by apply-modmorph.
		     (setf (module-decl-form module) modexp)
		     module)))))))))

;;; EVAL-VIEW-ARG : Arg Module pre-maps -> Arg'
;;;  Arg == (%!arg formal-arg-name View)
;;; note: mod is evaluated
;;; returns canonicalized arg
;;; 
(defun eval-view-arg (arg mod pre-maps)
  (let ((arg-name (%!arg-name arg))
	(vw (%!arg-view arg)))
    (unless (%is-view vw) (break "Invalid view in instantition!"))	; panic
    (%!arg* arg-name
	    (complete-view vw arg-name mod pre-maps))))

;;; *************
;;; CREATE-RENAME : modexp -> module
;;  *************
;;; create module and then rename.
;;;
(defun find-renaming-sort-in (mod name type)
  (let ((sort (find-sort-in mod name)))
    (unless sort
      (with-output-chaos-error ('no-such-sort)
	(princ "sort is not found for rename.")
	(print-sort-ref name)
	))
    (when (and sort (eq *chaos-module* (sort-module sort)))
      (with-output-chaos-error ('sort-hard-wired)
	(format t "sorry! sort `~a' is hard-wired, cannot be renamed."
		(string (sort-id sort)))
	))
    (when (or (and (eq type :visible) (sort-is-hidden sort))
	      (and (eq type :hidden) (not (sort-is-hidden sort))))
      (with-output-chaos-error ('sort-type-error)
	(format t "~a must be ~a for `~a' renaming."
		(string (sort-id sort))
		type
		(if (eq type :visible)
		    "sort"
		    "hsort")
		)
	))
    sort))

(defun create-rename (modexp)
  (flet ((report-error (&rest ignore)
	   (declare (ignore ignore))
	   (with-output-msg ()
	     (princ "could not evaluate the renaming: ")
	     (print-modexp modexp)
	     (chaos-error 'modexp-error))))
    (cond ((int-rename-p modexp)	; internal evaluated
	   (let* ((newmod (!create-module modexp))
		  (target-mod (eval-modexp* (int-rename-module modexp)))
		  (modmap (acons target-mod newmod nil))
		  (map (create-modmorph modexp
					(int-rename-sort-maps modexp)
					(int-rename-op-maps modexp)
					modmap)))
	     (with-in-module (newmod)
	       (apply-modmorph-internal map target-mod newmod))
	     newmod))
	  (t				; pure modexp
	   ;; create new module from the scratch.
	   (let ((target-module nil))
	     (with-chaos-error (#'report-error)
	       ;; target must be global
	       (setq target-module (eval-modexp (%rename-module modexp)))
	       (when *on-modexp-debug*
		 (with-output-msg()
		   (format t "create rename: target = ")
		   (print-modexp target-module)))
	       (when (modexp-is-error target-module)
		 (with-output-chaos-error ('no-such-module)
		   (princ "no such module: ")
		   (print-modexp (%rename-module modexp))))
	       (setf (%rename-module modexp) target-module)
	       (let* ((mod target-module)
		      (ren (if (%is-rmap (%rename-map modexp))
			       (%rmap-map (%rename-map modexp))
			     (%rename-map modexp)))
		      (mod-name modexp)	; dummy at this time, will changed by
					; int-rename later.
		      (newmod (!create-module mod-name))
		      (modmap (acons mod newmod nil))
		      (map (create-modmorph modexp nil nil modmap)))
		 ;;
		 (let ((check (is-rename-injective ren)))
		   (when (eq check :warn)
		     (with-output-chaos-warning ()
		       (princ "rename map may not be injective: ")
		       (print-modexp modexp)))
		   (when (eq check :invalid)
		     (with-output-chaos-error ()
		       (princ "invalid rename map: ")
		       (print-modexp modexp))))
		 ;;
		 (dolist (x (cadr (assq '%ren-sort ren)))
		   (let ((sort (find-renaming-sort-in mod (car x) :visible)))
		     ;; NOTE: `rename-sort' may modify module map & sort map
		     ;;        iff it generates a dummy module.
		     (rename-sort map mod newmod sort (%sort-ref-name (cadr x)))))
		 ;; 
		 (dolist (x (cadr (assq '%ren-hsort ren)))
		   (let ((sort (find-renaming-sort-in mod (car x) :hidden)))
		     (rename-sort map mod newmod sort (%sort-ref-name (cadr x)))))
		 
		 ;; generate new operator (opinfo + methods) with making
		 ;; operator map in map. 
		 ;; `rename-op' may modify module map iff it generated a dummy
		 ;; module. 
		 ;; operator map is set by `rename-op'.
		 (dolist (x (cadr (assq '%ren-op ren)))
		   (let ((opinfos (find-qual-operators (car x) mod ':functional)))
		     (unless opinfos
		       (with-output-chaos-error ('no-such-operator)
			 (princ "operator not found in rename: ")
			 (print-ast (car x))
			 (princ " in module ") (print-modexp mod)))
		     (dolist (opinfo opinfos)
		       (rename-op map mod newmod opinfo (cadr x) mod))))
		 ;; 
		 (dolist (x (cadr (assq '%ren-bop ren)))
		   (let ((opinfos (find-qual-operators (car x) mod ':behavioural)))
		     (unless opinfos
		       (with-output-chaos-error ('no-such-operator)
			 (princ "behavioural operator not found in rename: ")
			 (print-ast (car x))
			 (princ " in module ") (print-modexp mod)))
		     (dolist (opinfo opinfos)
		       (rename-op map mod newmod opinfo (cadr x) mod))))
		 ;; we must make maps of SortId constants iff the
		 ;; coressponding sort is mapped.
		 (dolist (s-map (modmorph-sort map))
		   (let* ((source (car s-map))
			  (target (cdr s-map))
			  (old-name (list (string (sort-id source))))
			  (new-name (list (string (sort-id target))))
			  (s-opinfo nil)
			  (s-method nil))
		     (setq s-opinfo (find-operators-in-module
				     old-name
				     0
				     mod
				     ':functional))
		     (when (cdr s-opinfo)
		       (with-output-chaos-error ('too-may-opinfos)
			 (princ "automatic generation of operator renaming failed")
			 (format t "~& for SortId ~a" old-name)))
		     (setq s-opinfo (car s-opinfo))
		     (with-in-module (mod)
		       (setq s-method (lowest-method* (car (opinfo-methods s-opinfo)))))
		     (unless (*find-method-in-map (modmorph-op map) s-method)
		       (rename-op map mod newmod s-opinfo new-name mod))))

		 ;; now we've constructed the maps,
		 ;; we can make real module name here.
		 (setq mod-name (make-int-rename :module mod
						 :sort-maps (modmorph-sort map)
						 :op-maps (modmorph-op map)))
		 (setf (module-name newmod) mod-name)
		 ;;
		 ;; finally, apply generated modmorph.
		 ;;
		 (with-in-module (newmod)
		   (apply-modmorph-internal map mod newmod))
		 (setf (module-decl-form newmod) modexp)
		 newmod )))))))

;;; EOF

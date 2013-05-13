;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: substitution.lisp,v 1.5 2010-05-30 04:34:42 sawada Exp $
(in-package :chaos)
#|==============================================================================
				 System: Chaos
			       Module: primitives
			    File: substitution.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

#|
				  SUBSTITUTION
--------------------------------------------------------------------------------
 A substitution is a map from variables to terms. Any mapping \sigma of variables
 to terms extends to a substitution by defining \sigma(f(t1,...,tn)) to be
 f(\sigma(t1), ... , \sigma(tn)).

 IMPLEMENTATION:
 this is naturally an association list of (varible . term) pair, and we want it
 to be mutable, then we implemented as a structure of type list.
--------------------------------------------------------------------------------
|#

;;(defstruct (substitution (:type list)
;;                         (:copier nil)
;;                         (:constructor substitution-create (bindings)))
;;  (bindings nil))                       ; a list of pair (variable . term) 
;;

(defmacro substitution-create (_bind) _bind)
(defmacro substitution-bindings (_sub) _sub)
(defmacro assoc-in-substitution (_key _sub &optional (_test '#'variable-eq))
  `(assoc ,_key ,_sub :test ,_test))

;;; CREATE-EMPTY-SUBSTITUTION
;;; Creates new empty substitution
;;;
(defmacro create-empty-substitution () `())
(defun new-substitution () ())

;;; SUBSTITUTION-COPY sigma
;;; Returns a copy of sigma.
;;;
(defmacro substitution-copy (_sigma)
  ` (mapcar #'(lambda (map)
		(cons (car map) (cdr map)))
	    ,_sigma))

;;; SUBSTITUTION-IS-EMPTY sigma
;;; Returns t iff \sigma is an empty substitution-
;;;
(defmacro substitution-is-empty (sigma_) `(null ,sigma_))

;;; SUBSTITUTION-DOMAIN sigma
;;; Returns the domain of sigma
;;;
(defmacro substitution-domain (_sigma_) `(mapcar #'car ,_sigma_))

;;; VARIABLE-IMAGE
;;; returns the image of variable under sigma.
;;;
(defmacro variable-image (*_sigma *_variable)
  `(cdr (assoc ,*_variable ,*_sigma :test #'variable-eq)))

(defmacro variable-image-fast (_*sigma _*variable)
  `(cdr (assoc ,_*variable ,_*sigma :test #'eq)))

(defmacro variable-image-slow (_*sigma _*variable)
  `(cdr (assoc ,_*variable ,_*sigma :test #'variable=)))

;;; SUBSTITUTION-LIST-OF-PAIRS sigma
;;; returns the list of pair in substitution-
;;;
(defmacro substitution-list-of-pairs (*_sigma_*) *_sigma_*)

;;; SUBSTITUTION-ADD sigma variable term
;;; adds the new map variable -> term to sigma.
;;;
(defmacro substitution-add (sigma_* variable_* term_*)
  `(cons (cons ,variable_* ,term_*) ,sigma_*))

;;; SUBSTITUTION-DELETE sigma variable
;;; deletes the map for variable from sigma.
;;; NOTE: sigma is modified.
;;;
(defmacro substitution-delete (sigma!_ variable!_)
  (once-only (sigma!_)
    ` (progn (setf ,sigma!_
		   (delete ,variable!_ ,sigma!_ :test #'variable-eq))
	     ,sigma!_)))

;;; SUBSTITUTION-CHANGE sigma variable term
;;; change the mapping of variable to term.
;;; if the variable is not in the domain of sigma, add the new binding.
;;; NOTE: sigma is modified.
;;;
(defmacro substitution-change (?__sigma ?__variable ?__term)
  (once-only (?__sigma ?__variable ?__term)
    ` (let ((binding (assoc-in-substitution ,?__variable ,?__sigma)))
	(if binding
	    (setf (cdr binding) ,?__term)
	    (push (cons variable ,?__term) ?__sigma))
	,?__sigma)))

;;; SUBSTITUTION-SET sigma variable term
;;; Changes sigma to map v to term.
;;;
(defmacro substitution-set (?_?sigma ?_?v ?_?term)
  (once-only (?_?sigma ?_?v ?_?term)
     `(progn
        (if (variable-eq ,?_?v ,?_?term)
	    (substitution-delete ,?_?sigma ,?_?v)
	    (substitution-change ,?_?sigma ,?_?v ,?_?term))
       ,?_?sigma)))

;;; CANONICALIZE-SUBSTITUTION : substitution -> substitution
;;;
(defun canonicalize-substitution (s)
  (declare (type list s)
	   (values list))
  (sort	 (copy-list s)			; (substitution-copy s)		
	 #'(lambda (x y)		; two substitution items (var . term)
	     (string< (the simple-string (string (variable-name (car x))))
		      (the simple-string (string (variable-name (car y))))))))


;;; SUBSTITUTION-EQUAL : substitution1 substitution2 -> Bool
;;;
(defun substitution-equal (s1 s2)
  (declare (type list s1 s2)
	   (values (or null t)))
  (every2len #'(lambda (x y)
		 (and (variable= (the term (car x)) (the term (car y)))
		      (term-is-similar? (the term (cdr x)) (the term (cdr y)))))
	     s1 s2))

;;; SUBSTITUTION-RESTRICT : list-of-variables substitution -> substitution
;;;
(defun substitution-restrict (vars sub)
  (declare (type list vars sub)
	   (values list))
  (let ((res nil))
    (dolist (s sub)
      (when (member (car s) vars)
	(push s res)))
    res))

;;; SUBSTITUTION-SUBSET substitution-1 substitution-2 : -> bool
;;; subset when viewed as a set of (mapping) pairs
;;; assumed canonicalized
;;;
(defun substitution-subset (s1 s2)
  (declare (type list s1 s2)
	   (values list))
  (substitution-subset-list (substitution-list-of-pairs s1)
			    (substitution-list-of-pairs s2)))
(defun substitution-subset-list (s1 s2)
  (declare (type list s1 s2)
	   (values (or null t)))
  (let ((s1x s1)
	(s2x s2)
	(res t))
    (loop (when (null s1x) (return))
	  (let ((v1 (the term (caar s1x)))
		(t1 (the term (cdar s1x))))
	    (loop (when (null s2x) (setq res nil) (return))
		  (when (variable-eq v1 (caar s2x))
		    (if (term-is-similar? t1 (cdar s2x))
			(progn (setq s2x (cdr s2x)) (return))
			(progn (setq res nil) (return))))
		  (setq s2x (cdr s2x)))
	    (when (null res) (return))
	    (setq s1x (cdr s1x))))
    res))


;;; SUBSTITUTION-DOMAIN-RESTRICTION sigma domain
;;; Restricts the domain of sigma to dom and renames in a canonical fashion all
;;; variables in the range of sigma, but not in domain. More precisely, returns
;;; a substitution sigma2 with domain a subset of domain such that, for any
;;; variable v in domain, \sigma2(v) = \rho(\sigma(v)), where \rho is a substitution
;;; that renames variables. 
;;;
;;; TODO
(defun substitution-domain-restriction (sigma domain)
  sigma domain
  )

;;; SUBSTITUTION-UNION sigma1 sigma2
;;; Returns the union of \sigma1 nd \sigma2. Returns 'incompatible if
;;; \sigma1(v) differs from \sigma2(v) for some v in the intersection of their
;;; domains. 
;;;
;;; TODO
(defun substitution-union (sigma1 sigma2)
  sigma1 sigma2
  )

;;; SUBSTITUTION-COMPOSIT sigma1 sigma2
;;; Returns the composition of \sigma1 and \sigma2. The result of applying this
;;; composition to a term t is \sigma1(\sigma2(t)).
;;; NOTE: This operation is NOT commutative,
;;;       i,e. substitution-composit(sigma, sigma) =/= sigma.
;;;
(defun substitution-composit (sigma1 sigma2)
  sigma1 sigma2
  )

;;; SUBSTITUTION-FOREACH (element sigma) body
;;; Yields the variable-term pairs in sigma
;;;
(defmacro substitution-foreach ((?_??element ?_??sigma) &body ?_??body)
  `(dolist (,?_??element (substitution-bindings ,?_??sigma))
     ,@?_??body)
  )

;;; SUBSTITUTION-IMAGE 
;;; Returns sigma(t) and "true" iff the sort of "t" and "sigma(t)" are the same.
;;; A COPY of the term "t" is done and the sort information is updated.
;;;

(defun substitution-image (sigma term)
  (declare (type list sigma)
	   (type term term)
	   (values term (or null t)))
  (let ((*consider-object* t))
    (cond ((term-is-variable? term)
	   (let ((im (variable-image sigma term)))
	     (if im;; i.e. im = sigma(term)
		 (values im nil)
		 (values term t))))
	  ((term-is-lisp-form? term)
	   (multiple-value-bind (new-term success)
	       (funcall (lisp-form-function term) sigma)
	     (if success
		 new-term
		 (throw 'rule-failure :fail-builtin))))
	  ((term-is-chaos-expr? term)
	   (multiple-value-bind (new-term success)
	       (funcall (chaos-form-expr term) sigma)
	     (if success
		 new-term
	       (throw 'fule-failure :fail-builtin))))
	  ((term-is-builtin-constant? term)
	   term)			; shold we copy?
	  (t (let ((l-result nil)
		   (modif-sort nil))
	       (dolist (s-t (term-subterms term))
		 (multiple-value-bind (image-s-t same-sort)
		     (substitution-image sigma s-t)
		   (unless same-sort (setq modif-sort t))
		   (push image-s-t l-result)))
	       (setq l-result (nreverse l-result))
	       (if modif-sort
		   (let ((term-image (make-term-with-sort-check (term-head term)
								l-result)))
		     (values term-image
			     (sort= (term-sort term)
				    (term-sort term-image))))
		   (values (make-applform (term-sort term)
					  (term-head term)
					  l-result)
			   t)))))))

(defun substitution-image! (sigma term)
  (declare (type list sigma)
	   (type term term)
	   (values term (or null t)))
  (let ((*consider-object* t))
    (cond ((term-is-variable? term)
	   (let ((im (variable-image-slow sigma term)))
	     (if im;; i.e. im = sigma(term)
		 (values im nil)
		 (values term t))))
	  ((term-is-lisp-form? term)
	   (multiple-value-bind (new-term success)
	       (funcall (lisp-form-function term) sigma)
	     (if success
		 new-term
		 (throw 'rule-failure :fail-builtin))))
	  ((term-is-chaos-expr? term)
	   (multiple-value-bind (new-term success)
	       (funcall (chaos-form-expr term) sigma)
	     (if success
		 new-term
	       (throw 'fule-failure :fail-builtin))))
	  ((term-is-builtin-constant? term) term) ; shold we copy?
	  (t (let ((l-result nil)
		   (modif-sort nil))
	       (dolist (s-t (term-subterms term))
		 (multiple-value-bind (image-s-t same-sort)
		     (substitution-image! sigma s-t)
		   (unless same-sort (setq modif-sort t))
		   (push image-s-t l-result)))
	       (setq l-result (nreverse l-result))
	       (if modif-sort
		   (let ((term-image (make-term-with-sort-check (term-head term)
								l-result)))
		     (values term-image
			     (sort= (term-sort term)
				    (term-sort term-image))))
		   (values (make-applform (term-sort term)
					  (term-head term)
					  l-result)
			   t)))))))

(defun substitution-image-cp (sigma term)
  (declare (type list sigma)
	   (type term term)
	   (values term (or null t)))
  (let ((*consider-object* t))
    (cond ((term-is-variable? term)
	   (let ((im (variable-image sigma term)))
	     (if im;; i.e. im = sigma(term)
		 (values (simple-copy-term im) nil)
		 (values term t))))
	  ((term-is-lisp-form? term)
	   (multiple-value-bind (new-term success)
	       (funcall (lisp-form-function term) sigma)
	     (if success
		 new-term
		 (throw 'rule-failure :fail-builtin))))
	  ((term-is-chaos-expr? term)
	   (multiple-value-bind (new-term success)
	       (funcall (chaos-form-expr term) sigma)
	     (if success
		 new-term
	       (throw 'fule-failure :fail-builtin))))
	  ((term-is-builtin-constant? term) term) ; shold we copy?
	  (t (let ((l-result nil)
		   (modif-sort nil))
	       (dolist (s-t (term-subterms term))
		 (multiple-value-bind (image-s-t same-sort)
		     (substitution-image-cp sigma s-t)
		   (unless same-sort (setq modif-sort t))
		   (push image-s-t l-result)))
	       (setq l-result (nreverse l-result))
	       (if modif-sort
		   (let ((term-image (make-term-with-sort-check (term-head term)
								l-result)))
		     (values term-image
			     (sort= (term-sort term)
				    (term-sort term-image))))
		   (values (make-applform (term-sort term)
					  (term-head term)
					  l-result)
			   t)))))))

(defun substitution-check-built-in (trm) trm)

;;; SUBSTITUTION-COMPOSE

(defun substitution-compose (teta lisp-term)
  (declare (type list teta lisp-term))
  (let ((fcn (lisp-form-function lisp-term))
	(new-fun nil)
	(new-term nil))
    (if (or #-CMU(typep fcn 'compiled-function)
	    #+CMU(typep fcn 'function)
	    (not (and (consp fcn) (eq 'lambda (car fcn))
		      (equal '(compn) (cadr fcn)))))
	(setf new-fun
	      `(lambda (compn) (funcall ',fcn (append ',teta compn))))
	(let ((oldteta (cadr (nth 1 (nth 2 (nth 2 fcn)))))
	      (realfcn (cadr (nth 1 (nth 2 fcn)))))
	  (setf new-fun
		`(lambda (compn)
		  (funcall ',realfcn (append ',(append teta oldteta) compn))))))
    (if (term-is-simple-lisp-form? lisp-term)
	(setf new-term (make-simple-lisp-form-term (lisp-form-original-form lisp-term)))
	(setf new-term (make-general-lisp-form-term (lisp-form-original-form lisp-term))))
    (setf (lisp-form-function new-term) new-fun)
    new-term))

(defun substitution-compose-chaos (teta chaos-expr)
  (declare (type list teta chaos-expr))
  (let ((fcn (chaos-form-expr chaos-expr))
	(new-fun nil)
	(new-term nil))
    (if (or #-CMU(typep fcn 'compiled-function)
	    #+CMU(typep fcn 'function)
	    (not (and (consp fcn) (eq 'lambda (car fcn))
		      (equal '(compn) (cadr fcn)))))
	(setf new-fun
	  `(lambda (compn) (funcall ',fcn (append ',teta compn))))
      (let ((oldteta (cadr (nth 1 (nth 2 (nth 2 fcn)))))
	    (realfcn (cadr (nth 1 (nth 2 fcn)))))
	(setf new-fun
	  `(lambda (compn)
	     (funcall ',realfcn (append ',(append teta oldteta) compn))))))
    (setf new-term (make-bconst-term *chaos-value-sort*
				     (list '|%Chaos|
					   new-fun
					   (chaos-original-expr chaos-expr))))
    new-term))

;;; SUBSTITUTION-IMAGE* sigma term
;;; Returns the image of term under sigma. Like substitution-image, but
;;; changing bound variables as necessary in the result to prevent variables in the
;;; range of sigma from being captured by a quantifier in term. Also renames all bound
;;; variables in the image of term under sigma (by replacing them by constants).
;;; To preserve shared subterms, returns t itself, and not a copy, if the image is the
;;; same as t.
;;; * TODO *
;;;

;; NO COPY of Term is done.
(defun substitution-image-no-copy (sigma term)
  (declare (type list sigma)
	   (type term term)
	   (values t))
  (let ((im nil))
    (cond ((term-is-variable? term)
	   (when (setq im (variable-image sigma term))
	     (term-replace term im)))
	  ((term-is-constant? term) ) ;; do nothing
	  (t (dolist (s-t (term-subterms term))
	       (substitution-image-no-copy sigma s-t))))))

(defun substitution-partial-image (sigma term)
  (declare (type list sigma)
	   (type term term))
  (let ((*consider-object* t))
    (cond ((term-is-variable? term)
	   (let ((im (variable-image sigma term)))
	     (if im
		 (values im nil)
		 (values term t))))
	  ((term-is-lisp-form? term)
	   (substitution-compose sigma term)
	   )
	  ((term-is-chaos-expr? term)
	   (substitution-compose-chaos sigma term))
	  ((term-is-builtin-constant? term) term)
	  ((term-is-applform? term)
	   (let ((l-result nil) (modif-sort nil))
	     (dolist (s-t (term-subterms term))
	       (multiple-value-bind (image-s-t same-sort)
		   (substitution-partial-image sigma s-t)
		 (unless same-sort (setq modif-sort t))
		 (push image-s-t l-result)))
	     (setq l-result (nreverse l-result))
	     (if modif-sort
		 (let ((term-image (make-term-with-sort-check 
				    (term-head term)
				    l-result)))
		   (values term-image
			   (sort= (term-sort term)
				  (term-sort term-image))))
		 (values (make-applform (term-sort term) (term-head term) l-result)
			 t))))
	  (t (break "substution-partial-image : not implemented ~s" term))
	  )))

(defun substitution-image-simplifying (sigma term &optional (cp nil) (slow-map nil))
  (declare (type list sigma)
	   (type term))
  (let ((*consider-object* t))
    ;; (setq subst-debug-term term)
    (cond ((term-is-variable? term)
	   (let ((im (if slow-map
			 (variable-image-slow sigma term)
		       (variable-image sigma term))))
	     (if im
		 (values (if cp
			     (progn
			       ;; debug
			       ;; (format t "~&copying " (term-print im))
			       (simple-copy-term im))
			   im)
			 (sort= (variable-sort term)
				(term-sort im)))
		 (values term t))))
	  ((term-is-chaos-expr? term)
	   (when *rewrite-debug*
	     (format t "CHAOS: ~S" (chaos-form-expr term)))
	   (multiple-value-bind (new-term success)
	       (funcall (chaos-form-expr term) sigma)
	     (if success
		 new-term
	       (throw 'fule-failure :fail-builtin))))
	  ((term-is-builtin-constant? term) term)
	  ((term-is-lisp-form? term)
	   (multiple-value-bind (new success)
	       (funcall (lisp-form-function term) sigma)
	     (if success
		 new
		 (throw 'rule-failure :fail-builtin))))
	  ((term-is-applform? term)
	   (let ((l-result nil)
		 (modif-sort nil))
	     (dolist (s-t (term-subterms term))
	       (multiple-value-bind (image-s-t same-sort)
		   (substitution-image-simplifying sigma s-t cp)
		 (unless same-sort (setq modif-sort t))
		 (push image-s-t l-result)))
	     (setq l-result (nreverse l-result))
	     (let ((method (term-head term)))
	       (if (and (cdr l-result)
			(null (cddr l-result))
			(method-is-identity method))
		   ;; head operator is binary & has identity theory
		   (if (term-is-zero-for-method (car l-result) method)
		       ;; ID * X --> X
		       ;; simplify for left identity.
		       (values (cadr l-result)
			       (sort= (term-sort term)
				      (term-sort (cadr l-result))))
		       ;; X * ID --> X
		       (if (term-is-zero-for-method (cadr l-result) method)
			   (values (car l-result)
				   (sort= (term-sort term)
					  (term-sort (car l-result))))
			   ;; X * Y 
			   (if modif-sort
			       (let ((term-image (make-term-with-sort-check 
						  method l-result)))
				 (values term-image
					 (sort= (term-sort term)
						(term-sort term-image))))
			       (values (make-applform (term-sort term)
						      method l-result)
				       t) ; sort not changed
			       )))	; done for zero cases
		   ;; This is the same as the previous bit of code
		   (if modif-sort
		       (let ((term-image (make-term-with-sort-check method
								    l-result)))
			 (values term-image
				 (sort= (term-sort term) (term-sort term-image))))
		       (values (make-applform (method-coarity method)
					      method l-result)
			       t))))))
	  (t (break "not implemented yet")) )))

;;; CANONICALIZE-SUBSTITUTION
;;;
(defun substitution-can (s)
  (declare (type list s)
	   (values list))
  (sort (copy-list s)
	#'(lambda (x y)			;two substitution items (var . term)
	    (declare (type list x y))
	    (string< (the simple-string (string (variable-name (car x))))
		     (the simple-string (string (variable-name (car y)))))
	    )))

;;;
(defun substitution-simple-image (teta term)
  (declare (type list teta)
	   (type term term))
  (macrolet ((assoc% (_?x _?y)
	       `(let ((lst$$ ,_?y))
		  (loop
		   (when (null lst$$) (return nil))
		   (when (eq ,_?x (caar lst$$)) (return (car lst$$)))
		   (setq lst$$ (cdr lst$$))))))
  (cond ((term-is-variable? term)
	 (let ((im (cdr (assoc% term teta))))
	   (if im im term)))
	((term-is-builtin-constant? term)
 	 (make-bconst-term (term-sort term)
			   (term-builtin-value term)))
	(t  (make-applform (method-coarity (term-head term))
			   (term-head term)
			   (mapcar #'(lambda (stm)
				       (substitution-simple-image teta stm))
				   (term-subterms term)))))))
;;; EOF

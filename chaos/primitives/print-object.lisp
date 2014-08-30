;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
;;;
;;; Copyright (c) 2000-2014, Toshimi Sawada. All rights reserved.
;;;
;;; Redistribution and use in source and binary forms, with or without
;;; modification, are permitted provided that the following conditions
;;; are met:
;;;
;;;   * Redistributions of source code must retain the above copyright
;;;     notice, this list of conditions and the following disclaimer.
;;;
;;;   * Redistributions in binary form must reproduce the above
;;;     copyright notice, this list of conditions and the following
;;;     disclaimer in the documentation and/or other materials
;;;     provided with the distribution.
;;;
;;; THIS SOFTWARE IS PROVIDED BY THE AUTHOR 'AS IS' AND ANY EXPRESSED
;;; OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
;;; WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
;;; ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
;;; DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
;;; DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE
;;; GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
;;; INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
;;; WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
;;; NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
;;; SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
;;;
(in-package :chaos)
#|==============================================================================
				 System: CHAOS
			       Module: primitives
			    File: print-object.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;;*****************************************************************************
;;; 			    INTERNAL OBJECT PRINTERS
;;;*****************************************************************************

;;;**********************
;;; Specific AST Printers______________________________________________________
;;;**********************

;;; SORT, SORT-REFERENCE
;;;----------------------------------------------------------------------------
(defun print-sort-ast (ast &optional (stream *standard-output*))
  (let ((*standard-output* stream))
    (let ((name (%sort-ref-name ast))
	  (qual (%sort-ref-qualifier ast)))
      (format t "~&Sort : ~a" name)
      (when qual
		(format t "~& qualified by the module expression: ")
		(print-modexp qual stream t t)))))

(defun print-sort-ref (ast &optional (stream *standard-output*))
  (if (%is-sort-ref ast)
      (let ((*standard-output* stream)
	    (name (%sort-ref-name ast))
	    (qual (%sort-ref-qualifier ast)))
	(if qual
	    (progn
	      (format t "~a." name) 
	      (print-modexp qual stream t t))
	  (format t "~a" name)))
    (princ ast)))

;;;(B)SORT/SUBSORT DECLARATION
;;;---------------------------------------------------------------------------

;;; SORT DECLARATION
(defun print-sort-decl (ast &optional (stream *standard-output*))
  (format stream "(%sort-decl ~s ~s)" (%sort-decl-name ast)
	  (%sort-decl-hidden ast)))

;;; SUBSORT DECLARATION
(defun print-subsort-decl (ast &optional (stream *standard-output*))
  ;; #||
  (fresh-line)
  (let ((s-seq (remove nil (mapcar #'(lambda (x)
				       (if (atom x)
					   x
					 (%sort-ref-name x)))
				   (%subsort-decl-sort-relation ast)))))
    (format stream "~&Subsort declaration : ~{~a~^ ~a ~}" s-seq))
  ;; ||#
  #||
  (format stream
	  "(%subsort-decl ~{~s~^ ~s ~})"
	  (%subsort-decl-sort-relation ast))
  ||#
  )

;;; BSORT DECLARATION
(defun print-bsort-decl (ast &optional (stream *standard-output*))
  (let ((tp (%bsort-decl-token-predicate ast))
	(tc (%bsort-decl-term-creator ast))
	(tpr (%bsort-decl-term-printer ast))
	(td (%bsort-decl-term-predicate ast)))
  (format stream "(%bsort-decl ~s ~s ~s ~s ~s ~s)" (%bsort-decl-name ast)
	  tp tc tpr td
	  (%bsort-decl-hidden ast))
  #||
  (when tp
    (format stream "~&  token predicate = ~a" tp))
  (when tc
    (format stream "~&  term creator    = ~a" tc))
  (when tpr
    (format stream "~&  term printer    = ~a" tpr))
  (when td
    (format stream "~&  term predicate  = ~a" tp))
  ||#
  ))

;;; PRINCIPAL-SORT-DECLARATION
(defun print-psort-decl (ast &optional (stream *standard-output*))
  #||
  (format stream "~&Principal sort declaration : ~a"
	  (%psort-decl-sort ast))
  ||#
  (format stream "(%psort-decl ~s)" (%psort-decl-sort ast)))

;;; Operator Reference
;;;-----------------------------------------------------------------------------
(defun print-opref (ast &optional (stream *standard-output*))
  #||
  (let ((*standard-output* stream)
	(name (%opref-name ast))
	(module (%opref-module ast))
	(numargs (%opref-num-args ast)))
    (format t "~&operator reference : name = ~a" name)
    (format t "~&                   module = ")
    (print-modexp module stream t t)
    (when numargs
      (format t "~&      number of arguments = ~d" numargs)))
  ||#
  (format stream "~s ~s ~s" (%opref-name ast)
	  (%opref-module ast)
	  (%opref-num-args ast))
  )

(defun print-opref-simple (ast &optional (stream *standard-output*))
  (let ((*standard-output* stream)
	(name (%opref-name ast))
	(module (%opref-module ast)))
    (if (cdr name)
	(princ name)
	(princ (car name)))
    (when module
      (princ ".")
      (print-modexp module stream t t))))

;;; Operator Declaration *TODO*
;;;-----------------------------------------------------------------------------
(defun print-op-decl-ast (ast &optional (stream *standard-output*))
  (let ((*standard-output* stream)
	(name (%op-decl-name ast))
	(arity (%op-decl-arity ast))
	(coarity (%op-decl-coarity ast))
	(attr (%op-decl-attribute ast)))
    (format t "Operator declaration:")
    (let ((*print-indent* (+ 2 *print-indent*)))
      (print-next)
      (format t "symbol = ~a" name)
      (print-next)
      (format t "arity = ")
      (if arity
	  (let ((flg nil))
	    (dolist (s arity)
	      (if flg (princ " ") (setf flg t))
	      (print-sort-ref s)))
	  (princ "NONE"))
      (print-next)
      (format t "coarity = ")
      (print-sort-ref coarity)
      (when attr
	(print-opattrs-ast attr)))))

;;; Operator Attribute declarations
;;;-----------------------------------------------------------------------------
#||
(defun print-opattr-decl (ast &optional (stream *standard-output*))
  (let ((opref (%opattr-decl-opref ast))
	(attribute (%opattr-decl-attribute ast)))
    (print-opref opref stream)
    (print-opattrs-ast attribute stream)))

||#

(defun print-opattrs-ast (ast &optional (stream *standard-output*))
  (let ((theory (%opattrs-theory ast))
	(assoc (%opattrs-assoc ast))
	(prec (%opattrs-prec ast))
	(strat (%opattrs-strat ast))
	(memo (%opattrs-memo ast))
	(constr (%opattrs-constr ast))
	(coherent (%opattrs-coherent ast)))
    (format stream "~&attributes : ")
    (when theory
      (format stream "~& - theory ~a" theory))
    (when assoc
      (format stream "~& - associativity ~a" assoc))
    (when prec
      (format stream "~& - precedence ~a" prec))
    (when strat
      (format stream "~& - strategy ~a" strat))
    (when memo
      (format stream "~& - memo is specified"))
    (when constr
      (format stream "~& - constr is specified"))
    (when coherent
      (format stream "~& - coherent is specified"))
    ))

;;; Variable Declaration
;;;-----------------------------------------------------------------------------
(defun print-var-decl (ast &optional (stream *standard-output*))
  (let* ((*standard-output* stream)
	 (names (%var-decl-names ast))
	 (sort-ref (%var-decl-sort ast))
	 (sort-name (%sort-ref-name sort-ref))
	 (sort-qual (%sort-ref-qualifier sort-ref)))
    (format t "~&Variable declaration : names =~{ ~a~}" names)
    (format t "~&  Sort = ~a" sort-name)
    (when sort-qual
      (princ ".")
      (print-modexp sort-qual stream t t))))
    
(defun print-pvar-decl (ast &optional (stream *standard-output*))
  (let* ((*standard-output* stream)
	 (names (%pvar-decl-names ast))
	 (sort-ref (%pvar-decl-sort ast))
	 (sort-name (%sort-ref-name sort-ref))
	 (sort-qual (%sort-ref-qualifier sort-ref)))
    (format t "~&Pseud variable declaration : names =~{ ~a~}" names)
    (format t "~&  Sort = ~a" sort-name)
    (when sort-qual
      (princ ".")
      (print-modexp sort-qual stream t t))))

;;; LET DECLARATOIN
;;;-----------------------------------------------------------------------------
(defun print-let-decl (ast &optional (stream *standard-output*))
  (let ((sym (%let-sym ast))
	(value (%let-value ast)))
    (format stream "~&let declaration: ")
    (format stream "~&  symbol = ~a" sym)
    (format stream "~&  value  = ~a" value)))

;;; MACRO DECLARATION
;;;-----------------------------------------------------------------------------
(defun print-macro-decl (ast &optional (stream *standard-output*))
  (let ((lhs (%macro-lhs ast))
	(rhs (%macro-rhs ast)))
    (format stream "~&macro declaration:")
    (format stream "~% LHS = ~a" lhs)
    (format stream "~% RHS = ~a" rhs)))

;;; AXIOM DECLARATION
;;;-----------------------------------------------------------------------------
(defun print-axiom-decl-form (ast &optional (stream *standard-output*))
  (let ((type (%axiom-decl-type ast))
	(labels (%axiom-decl-labels ast))
	(lhs (%axiom-decl-lhs ast))
	(rhs (%axiom-decl-rhs ast))
	(cond (%axiom-decl-cond ast)))
    (format stream "~&axiom declaration(~a): " type)
    (if labels
	(format stream " labels =~{~a ~}" labels))
    (format stream "~& lhs = ~a" lhs)
    (format stream "~& rhs = ~a" rhs)
    (if cond
	(format stream "~& condition = ~a" cond))))

;;; IMPORT-DECLARATION
;;;-----------------------------------------------------------------------------
(defun print-import-decl (ast &optional (stream *standard-output*))
  (let ((mode (%import-mode ast))
	(mod (%import-module ast))
	(as (%import-alias ast)))
    (format stream "import declaration : ")
    (format stream "mode = ~a, " mode)
    (when as
      (format stream "as ~a, " as))
    (format stream "module = ")
    (print-modexp mod)))

;;; MODULE EXPRESSION
;;;-----------------------------------------------------------------------------
;;; printers of module expressions are rather special, because
;;; they may include internal objects (not AST).
;;;
(defun print-modexp-simple (me &optional (stream *standard-output*))
  (print-modexp me stream t t))

;;; top level modexp printer ---------------------------------------------------

#||
(defun get-context-name (obj)
  (let ((context-mod (object-context-mod obj)))
    (if context-mod
	(with-output-to-string (str)
	  (print-mod-name context-mod str t))
      nil)))
||#

(defun get-context-name (obj)
  (let ((context-mod (object-context-mod obj)))
    (if context-mod
	(get-module-print-name context-mod)
      nil)))

(defun get-context-name-extended (obj &optional (context *current-module*))
  (let ((cmod (object-context-mod obj)))
    (unless cmod (return-from get-context-name-extended nil))
    ;;
    (when context
      (let ((als (assoc cmod (module-alias context))))
	(when als
	  (return-from get-context-name-extended (cdr als)))))
    ;;
    (let ((name (get-module-print-name cmod)))
      (unless (module-is-parameter-theory cmod)
	(cond ((modexp-is-simple-name name) 
	       (return-from get-context-name-extended name))
	      (t (return-from get-context-name-extended
		   (with-output-to-string (str)
		     (print-modexp-simple name str))))))
      ;; parameter
      (format nil "parameter ~A of module ~A"
	      (car name)
	      (get-module-print-name (fourth name))))))

(defun print-modexp (me &optional
			(stream *standard-output*)
			(simple t)
			(no-param nil))
  (let ((.file-col. .file-col.)
	(*standard-output* stream))
    (if me
	(cond
	 ;;
	 ;; The modexp internal..
	 ((int-plus-p me) (pr-int-plus me stream simple no-param))
	 ((int-rename-p me) (pr-int-rename me stream simple no-param))
	 ((int-instantiation-p me)
	  (pr-int-instantiation me stream simple no-param))
	 ;; simple module expr
	 ((stringp me) (princ me stream)
		       (print-check .file-col. 0 stream))
	 ((module-p me) (print-mod-name me stream simple no-param)
			(print-check .file-col. 0 stream))
	 ;; view structure
	 ((view-struct-p me)
	  (if simple
	      (if (eq (view-name me) :anon-view)
		  (print-modexp (view-source me) stream simple no-param)
		(progn (princ (view-name me) stream)
		       (print-check .file-col. 0 stream)))
	    (print-view me stream simple no-param)))
	 ;; special expressions used internally, not defined as AST but
	 ;; is generated on the fly.
	 ;; what is this? => '("ModuleName"). I'm not sure this can really happen,
	 ;; but our reader routine tends to consing an atom.
	 ;; anyway, the cost is not so high.
	 ((and (consp me)
	       (stringp (car me))
	       (null (cdr me)))
	  (print-modexp (car me) stream simple no-param))
	 ((modexp-is-error me)
	  (princ "(")
	  (incf .file-col.)
	  (print-simple-princ-open (cdr me) stream)
	  (princ ")")
	  (decf .file-col.))
	 ((modexp-is-?name? me)
	  (print-modexp (?name-name me) stream simple no-param))
	 ((modexp-is-parameter-theory me)
	  (let ((cntxt (fourth me)))
	    (princ (car me))
	    (when (and cntxt (not (eq *current-module* cntxt)))
	      (princ ".")
	      (print-mod-name cntxt stream t t)
	      (print-check .file-col. 0 stream))))
	 ((%is-modexp me)
	  (print-modexp (%modexp-value me) stream simple no-param))

	 ;; modexp or other ast in general.
	 ((chaos-ast? me)
	  (let* ((type (ast-type me))
		 (printer (get type ':print)))
	    (if printer
		(if (memq (ast-type me) '(%rmap %ren-sort %ren-op %ren-var
					  %ren-param %+ %* %*view %! %view
					  %prim-view %view-under %view-from
					  %view-mapping))
		    (funcall printer me stream simple no-param)
		  (funcall printer me stream))
	      (print-chaos-object me stream))))
	 (t				; ???
	  (print-chaos-object me stream)))
      (princ "None."))))

;;; specific Modexp printers ---------------------------------------------------

;;; *** PLUS ****

(defun print-plus-modexp (me &optional stream simple no-param)
  (let ((flg nil))
    (do* ((args (reverse (%plus-args me)) (cddr args))
	  (l (car args) (car args))
	  (r (cadr args) (cadr args)))
	 ((null args))
      (when flg
	(princ " + " stream)
	(print-check .file-col. 0 stream))
      (print-modexp l stream simple no-param)
      (when r
	(setq .file-col. (1- (file-column stream)))
	(princ " + " stream)
	(setq flg t)
	(if (%is-plus r)
	    (progn (princ "(" stream)
		   (incf .file-col.)
		   (print-modexp r stream simple no-param)
		   (princ ")" stream)
		   (decf .file-col.))
	    (print-modexp r stream simple no-param))))))

;;; *** RENAME ***

(defun print-rename-modexp (me &optional stream simple no-param)
  (print-modexp (%rename-module me) stream simple no-param) (princ " * {")
  (print-check .file-col. 0 stream)
  (if simple
      (princ " ... " stream)
    (print-rename-map (%rename-map me) stream)
    )
  (princ "}" stream))

;;; OBSOLETE
;;; *** VIEW-RENAME ***

#||
(defun print-view-rename-modexp (me &optional stream simple no-param)
  (princ "*view|| " stream)
  (print-modexp (%view-rename-view me) stream simple no-param)
  (princ " ||*{" stream)
  (if simple
      (princ " ... " stream)
      (print-rename-map (%view-rename-map me) stream))
  (princ "}" stream))
||#

;;; *** INSTANTIATION ***

(defun print-instantiation-modexp (me &optional stream simple no-param)
  (if (or (stringp (%instantiation-module me))
	  (and (module-p (%instantiation-module me))
	       (stringp (module-name (%instantiation-module me)))))
      (progn
	(print-modexp (%instantiation-module me) stream simple no-param))
      (progn
	;; (princ "(" stream)
	(print-modexp (%instantiation-module me) stream simple no-param)
	;; (princ ")" stream)
	))
  ;; (princ "[" stream)
  (princ "(" stream)
  (incf .file-col.)
  (let ((flg nil)
	(pos-arg nil))
    (dolist (arg (%instantiation-args me))
      (let ((arg-name (%!arg-name arg))
	    (view (%!arg-view arg)))
	(if flg
	    (progn (princ ", " stream)
		   (print-check .file-col. 0 stream))
	    (setq flg t))
	;;
	(cond ((stringp arg-name) (princ arg-name stream))
	      ((and (consp arg-name) (cdr arg-name))
	       ;; (format t "~a@" (car arg-name))
	       (format t "~a." (car arg-name))
	       (print-chaos-object (cdr arg-name) stream))
	      ((consp arg-name) (princ (car arg-name) stream))
	      (t (let ((na (get-module-nth-arg-name
			    (%instantiation-module me)
			    arg-name)))
		   (setq pos-arg t)
		   (when na
		     (setq pos-arg nil)
		     (princ na stream)))))
	;;
	(unless pos-arg
	  (princ " <= " stream))
	(print-view-modexp-abbrev view stream simple))))
  ;; (princ "]" stream)
  (princ ")" stream)
  (decf .file-col.)
  )

;;; *** Sort renaming ***

(defun print-ren-sort (ast &optional (stream *standard-output*) pretty)
  (let ((*standard-output* stream)
	(p-flg nil))
    (dolist (elt (%ren-sort-maps ast))
      (if p-flg
	  (progn (princ ",")
		 (print-check .file-col. 0 stream))
	(setq p-flg t))
      (when pretty (print-next))
      (princ "sort ")
      (print-sort-ref (car elt))
      (print-check .file-col. 0 stream)
      (princ " -> ")
      (print-sort-ref (cadr elt)))))
    
;;; *** Operator renaming ***

(defun print-ren-op (ast &optional (stream *standard-output*) pretty)
  (let ((*standard-output* stream)
	(p-flg nil))
    (dolist (elt (%ren-op-maps ast))
      (if p-flg (princ ",") (setq p-flg t))
      (when pretty (print-next))
      (princ "op ")
      (if (%is-opref (car elt))
	  (print-opref-simple (car elt))
	  (print-simple-princ-open (car elt)))
      (print-check .file-col. 0 stream)
      (princ " -> ")
      (if (%is-opref (cadr elt))
	  (print-opref-simple (cadr elt))
	  (print-simple-princ-open (cadr elt))))))

;;; Parameter renaming

(defun print-ren-param (ast &optional (stream *standard-output*))
  (let ((*standard-output* stream)
	source
	target)
    (dolist (elt (%ren-param-maps ast))
      (setq source (car elt))
      (setq target (cadr elt))
      (when (consp source) (setq source (car source)))
      (when (consp target) (setq target (car target)))
      (format stream "param ~a -> ~a~%" source target))))
    
;;; vars in mapping

(defun print-vars-ast (ast &optional (stream *standard-output*) pretty)
  (let ((p-flg nil))
    (dolist (elt (%vars-elements ast))
      (let ((var-names (car elt))
	    (sort (cadr elt)))
	(when pretty (print-next))
	(if p-flg (princ ",") (setq p-flg t))
	(if (cdr var-names)
	    (princ "vars" stream)
	    (princ "var" stream))
	(format stream "~{~^ ~a~} : " var-names)
	(print-sort-ref sort stream)))))
      
;;; *** RENAME MAP ***

(defun print-rename-map (rn &optional (stream *standard-output*) simple no-param pretty)
  (declare (ignore simple no-param))
  (let ((*standard-output* stream))
    (cond  ((null rn) (princ " ## EMPTY RENAME MAP ##")) ; for debugging.
	   ((%is-rmap rn)
	    (let ((flg nil))
	      (dolist (re (%rmap-map rn))
		(if flg
		    (progn (princ ", ")
			   (print-check .file-col. 0 stream))
		  (setq flg t))
		(when pretty (print-next))
		(print-ast re))))
	   (t (break "print-rename-map, not yet.")))))

;;;-----------------------------------------------------------------------------
;;; PRINTERS of INTERNAL MODEXP
;;;-----------------------------------------------------------------------------

;;; RENAME
(defun pr-int-rename (obj &optional (stream *standard-output*) simple no-param)
  ;; (declare (ignore simple no-param))
  (declare (ignore no-param))
  (let ((*standard-output* stream))
    #||
    (unless simple (format t "(%** "))
    ||#
    ;; (print-modexp (int-rename-module obj) stream simple no-param)
    (print-modexp (int-rename-module obj) stream t t)
    (princ " *{ " stream)
    (incf .file-col. 2)
    (if simple
	(princ " ... " stream)
	(let ((*print-indent* (+ *print-indent* 4))
	      (sort-maps (int-rename-sort-maps obj))
	      (op-maps (int-rename-op-maps obj)))
	  (print-next)
	  (let ((flg nil))
	    (dolist (smap sort-maps)
	      (if flg (progn (princ ",") (print-check .file-col. 0 stream))
		(setq flg t))
	      (print-sort-name (car smap))
	      (princ " -> ")
	      (print-sort-name (cdr smap))))
	  (let ((flg nil))
	    (dolist (omap op-maps)
	      ;; (method :simple . method)
	      (if flg (progn (princ ",")
			     (print-check .file-col. 0 stream))
		(setq flg t))
	      (princ "(") (print-chaos-object (car omap)) (princ ")")
	      (princ " -> ")
	      (princ "(") (print-chaos-object (cdr (last omap))) (princ ")")))
	  ))
    (if simple
	(princ " }")
	(princ " } )"))))
	  
;;; PLUS
(defun pr-int-plus (obj &optional (stream *standard-output*) simple no-param)
  (declare (ignore simple no-param))
  (let ((*standard-output* stream))
    #||
    (unless simple
      (format t "(%++ "))
    ||#
    (let ((*print-indent* (+ *print-indent* 4))
	  (flg nil))
      (dolist (mod (int-plus-args obj))
	(print-check)
	(when flg (princ " + "))
	;; (print-modexp mod stream simple no-param)
	(print-modexp mod stream t t)
	(setq flg t))
      #||
      (unless simple
	(princ " )"))
      ||#
      )))

;;; INSTATIATION
(defun pr-int-instantiation (obj &optional
				 (stream *standard-output*)
				 simple no-param)
  (declare (ignore simple no-param))
  (let ((*standard-output* stream))
    #||
    (unless simple
      (format t "(%!! "))
    ||#
    (let ((*print-indent* (+ *print-indent* 4)))
      ;; (print-modexp (int-instantiation-module obj) stream simple no-param)
      (print-modexp (int-instantiation-module obj) stream t t)
      ;; (princ "[ ")
      (princ "(")
      (let ((flg nil))
	(dolist (arg (int-instantiation-args obj))
	  (if flg (progn (princ ",") (print-next)) (setq flg t))
	  (let ((arg-name (%!arg-name arg))
		(pos-arg nil))
	    (cond ((stringp arg-name) (princ arg-name stream))
		  ((and (consp arg-name) (cdr arg-name))
		   ;; (format t "~a@" (car arg-name))
		   (format t "~a." (car arg-name))
		   (print-chaos-object (cdr arg-name) stream))
		  ((consp arg-name) (princ (car arg-name) stream))
		  (t (let ((na (get-module-nth-arg-name
				(int-instantiation-module obj)
				arg-name)))
		       (if na
			   (progn
			     (setq pos-arg nil)
			     (princ na stream))
			   (progn
			     (setq pos-arg t))))))
	    (unless pos-arg
	      (princ " <= "))
	    (let ((*print-indent* (+ *print-indent* 4)))
	      ;; (print-view (%!arg-view arg) stream simple no-param)
	      (print-view (%!arg-view arg) stream t t)
	      ))
	  (print-check)))
      ;; (princ " ]")
      (princ ")")
      )))

;;;-----------------------------------------------------------------------------
;;; Printers of VIEW & its friends.
;;;-----------------------------------------------------------------------------

(defun print-view-internal (vw &optional (stream *standard-output*) &rest ignore)
  (declare (ignore ignore))
  (print-view vw stream))

(defun print-view (vw &optional (stream *standard-output*) simple no-param
				(syntax *show-mode*))
  (if (eq syntax :cafeobj)
      (print-view-in-cafeobj-mode vw
				  stream simple
				  no-param)
    (print-view-in-chaos-mode vw
			      stream
			      simple
			      no-param)))

(defun print-view-in-cafeobj-mode (vw stream simple no-param)
  (cond ((and (not (stringp vw))
	      (chaos-ast? vw) 
              (memq (ast-type vw) 
                    '(%view %view-from %prim-view %view-from %view-mapping)))
	 (let ((printer (get (ast-type vw) ':print)))
	   (if printer
	       (funcall printer vw stream simple)
	       (print-chaos-object vw stream)))
	 )
	((view-p vw)
	 (let ((name (view-name vw))
	       (decl-form (view-decl-form vw)))
	   (if simple
	       (if (eq name :anon-view)
		   (print-modexp (view-source vw) stream t t)
		   (princ name stream))
	       (progn
		 (let ((*standard-output* stream)
		       (*print-indent* (+ 2 *print-indent*)))
		   (print-check)
		   (format stream "view ~a " name)
		   (princ "from ")
		   (if decl-form
		       (print-modexp (%view-module decl-form) stream simple no-param)
		       (print-modexp (view-src vw) stream simple no-param))
		   (princ " to ")
		   (if decl-form
		       (print-modexp (%view-target decl-form) stream simple no-param)
		       (print-modexp (view-target vw) stream simple no-param))
		   (princ " {")
		   (if decl-form
		       (print-abs-view-mapping (%view-map decl-form) stream simple no-param t)
		       (print-view-struct-maps vw stream simple no-param)))
		 (print-next)
		 (princ " }")))))
	;;
	;; AGGGHHHH!
	;;
	((and (consp vw) (stringp (car vw))) (princ vw stream))
        ((atom vw) (princ vw stream))
	(t (print-modexp vw stream simple no-param))
	))

(defun print-view-in-chaos-mode (vw stream &rest ignore)
  (declare (ignore ignore))
  (let ((*print-pretty* t))
    (format stream "~&~s" (object-decl-form vw))))

(defun print-view-struct-maps (view stream &rest ignore)
  (declare (ignore ignore))
  (let ((*print-indent* (+ *print-indent* 2))
	(sort-maps (view-sort-maps view))
	(op-maps (view-op-maps view))
	(*standard-output* stream)
	(flg nil))
    (dolist (sm sort-maps)
      (if flg (print-next) (setq flg t))
      (if (and (sort-struct-p (car sm))
	       (sort-is-hidden (car sm)))
	  (princ "hsort ")
	(princ "sort "))
      (print-chaos-object (car sm))
      (princ " -> ")
      (print-chaos-object (cdr sm)))
    (dolist (pm op-maps)
      (if flg (print-next) (setq flg t))
      (if (method-is-behavioural (term-head (car pm)))
	  (princ "bop ")
	(princ "op "))
      (princ "(")(print-chaos-object (term-head (car pm)))(princ ")")
      (princ " -> ")
      (princ "(")(print-chaos-object (term-head (cadr pm)))(princ ")")
      )))

(defun print-abs-view-mapping (map stream simple no-param pretty)
  (declare (ignore simple no-param))
  (unless map (return-from print-abs-view-mapping nil))
  (let ((rmap (if (%is-rmap map)
		  (%rmap-map map)
		  map)))
    (let ((smaps (assq '%ren-sort rmap))
	  (opmaps (assq '%ren-op rmap))
	  (vars (assq '%vars rmap))
	  (p-flg nil))
      (when vars (print-vars-ast vars stream pretty) (setq p-flg t))
      (when smaps
	(when p-flg (princ "," stream))
	(print-ren-sort smaps stream pretty) (setq p-flg t))
      (when opmaps
	(when p-flg (princ "," stream))
	(print-ren-op opmaps stream pretty)))))

(defun print-view-modexp (me &optional (stream *standard-output*) simple no-param)
  ;; (print-modexp (%view-target me) stream simple no-param)
  (when (%view-map me)
    (if simple
	(princ "{ ... }" stream)
	(let ((*standard-output* stream))
	  (print-check)
	  (princ "view")
	  (print-check)
	  (unless (eq 'none (%view-module me))
	    (princ " from ")
	    (print-modexp (%view-module me) stream simple no-param))
	  (princ " to ") (print-modexp (%view-target me) stream simple no-param)
	  (print-check)
	  (princ " {")
	  (let ((*print-indent* (+ 2 *print-indent*)))
	    (print-view-mapping (%view-map me) stream simple no-param))
	  (print-next)
	  (princ "  }")))))

(defun print-view-modexp-abbrev (me &optional
				    (stream *standard-output*) simple no-param)
  (let ((target (if (view-p me)
		    (view-target me)
		    (if (modexp-is-view me)
			(%view-target me)))))
      (if target
	  (print-modexp target stream simple no-param)
	  (if (stringp me)
	      (princ me)
	      (with-output-panic-message ()
		(format t "print-view, given invalid view : ")
		(prin1 me))))
		;; (chaos-error 'invalid-view))))
      (when (stringp me)
	(return-from print-view-modexp-abbrev nil))
      (when (and (not (view-p me)) (%view-map me))
	(if simple
	    (princ "{ ... }" stream)
	    (let ((*standard-output* stream))
	      (print-check)
	      (princ "{")
	      (print-check)
	      (print-view-mapping (%view-map me) stream)
	      (print-check)
	      (princ " }"))
	    ))))

(defun print-view-mapping (vwmap &optional
				 (stream *standard-output*) simple no-param
				 pretty)
  (unless vwmap (return-from print-view-mapping nil))
  (print-rename-map vwmap stream simple no-param pretty))

;;; ************************
;;; SPECIFIC OBJECT PRINTERS____________________________________________________
;;; ************************

;;; OPERATOR **********

(defun print-operator-internal (op &optional (stream *standard-output*))
  (format stream "~a/~a."
	  (operator-symbol op)
	  (operator-num-args op))
  (print-mod-name (operator-module op) stream))
	  
(defun print-op-name (op)
  (format t "~a/~a" (operator-symbol op) (operator-num-args op)))

;;; SORT **************

(defun print-sort-internal (sort &optional (stream *standard-output*) ignore)
  (declare (ignore ignore))
  (print-sort-name sort (or *current-module* *last-module*) stream))

(defun print-record-internal (sort &optional (stream *standard-output*) ignore)
  (declare (ignore ignore))
  (print-sort-name sort (or *current-module* *last-module*) stream))

(defun print-class-internal (sort &optional (stream *standard-output*) ignore)
  (declare (ignore ignore))
  (print-sort-name sort (or *current-module* *last-module*) stream))

(defun print-bsort-internal (sort &optional (stream *standard-output*) ignore)
  (declare (ignore ignore))
  (print-sort-name sort (or *current-module* *last-module*) stream))

(defun print-and-sort-internal (sort &optional (stream *standard-output*) ignore)
  (declare (ignore ignore))
  (print-sort-name sort (or *current-module* *last-module*) stream))

(defun print-or-sort-internal (sort &optional (stream *standard-output*) ignore)
  (declare (ignore ignore))
  (print-sort-name sort (or *current-module* *last-module*) stream))

(defun print-err-sort-internal (sort &optional (stream *standard-output*) ignore)
  (declare (ignore ignore))
  (print-sort-name sort (or *current-module* *last-module*) stream))

;;; MODULE ************

;;; (defun print-module-internal (module &optional (stream *standard-output*))
;;;  (print-mod-name module stream t t))

(defun print-module-internal (module &optional (stream *standard-output*) ignore)
  (declare (ignore ignore))
  (print-mod-name module stream t nil))

;;; AXIOM *************

(defun print-axiom-internal (ax &optional (stream *standard-output*) ignore)
  (declare (ignore ignore))
  (print-axiom-brief ax stream))

;;; REWRITE RULE *****
(defun print-rule-internal (rule &optional (stream *standard-output*) ignore)
  (declare (ignore ignore))
  (let ((cnd (not (term-is-similar? *BOOL-true* (rule-condition rule))))
	(.printed-vars-so-far. nil))
    (when (rule-labels rule)
      (print-rule-labels rule)
      (princ " "))
    (let ((.file-col. (file-column stream)))
      ;; LHS
      (setq .printed-vars-so-far.
	(term-print (rule-lhs rule) stream))
      (setq .file-col. (file-column stream))
      (print-check 0 .file-col.)
      (princ " --> ")
      (setq .file-col. (+ 5 .file-col.))
      ;; RHS
      (term-print (rule-rhs rule) stream)
      ;; CONDITION
      (when (or cnd (rule-id-condition  rule))
	(setq .file-col. (file-column stream))
	(print-check 0 .file-col.)
	(princ " if ")
	(setq .file-col. (+ 4 .file-col.))
	(when cnd
	  (term-print (rule-condition rule) stream))
	(when (and cnd (rule-id-condition rule))
	  (print-check)
	  (princ " and ")
	  (print-check))
	(when (rule-id-condition rule)
	    (print-id-condition (rule-id-condition rule) stream)))
	)))
  
;;; METHOD ************

(defun print-method-internal (meth &optional (stream *standard-output*) ignore)
  (declare (ignore ignore))
  (let ((mod (or *current-module* *last-module*))
	(.file-col. .file-col.))
    (format stream "~{~A~} :" (method-symbol meth))
    (setq .file-col. (file-column stream))
    (mapc #'(lambda (x)
	      (princ " " stream)
	      (print-sort-name x mod stream)
	      (print-check .file-col. 0 stream))
	  (method-arity meth))
    (print-check .file-col. 4 stream)
    (princ " -> ")
    (print-check .file-col. 0 stream)
    (print-sort-name (method-coarity meth) mod stream)))

;;; REAL PRINTERS **************************************************************

;;;-----------------------------------------------------------------------------
;;; MODMORPH printer. just for debugging.
;;;-----------------------------------------------------------------------------

(defun print-modmorph (mppg)
  (format t "~&Module morphism:")
  (format t "~& name: ") (print-chaos-object (modmorph-name mppg))
  (format t "~& sort: ")
  (dolist (i (modmorph-sort mppg))
    (print-check)
    (print-chaos-object (car i)) (princ "-->")
    (print-chaos-object (cdr i)) (princ " "))
  (format t "~& op: ")
  (dolist (i (modmorph-op mppg))
    (print-check)
    (print-chaos-object (car i)) (princ "-->")
    (print-chaos-object (cdr i)) (princ " "))
  (format t "~& module: ")
  (dolist (i (modmorph-module mppg))
    (print-check)
    (print-chaos-object (car i)) (princ "-->")
    (print-chaos-object (cdr i)) (princ " "))
  )

;;;-----------------------------------------------------------------------------
;;; MODULE NAME
;;;-----------------------------------------------------------------------------

(defun get-module-print-name (module)
  (unless (module-p module) (break "internal error, get-module-print-name"))
  (let ((name (module-name module)))
    (if (modexp-is-simple-name name)
	name
	(or (module-decl-form module) name))))

(defun make-module-print-name (mod &optional (abbrev t))
  (with-output-to-string (name-string)
    (print-mod-name mod name-string abbrev)
    name-string))

(defun print-mod-name (arg &optional
			   (stream *standard-output*)
			   (abbrev nil)
			   (no-param nil))
  (declare (values t))
  (let ((*standard-output* stream))
    (if (module-p arg)
	(let ((modname (get-module-print-name arg)))
	  (if (is-dummy-module arg)
	      (let ((info (getf (module-infos arg) 'rename-mod)))
		(print-mod-name (car info) stream abbrev no-param)
		(princ "*DUMMY"))
	      (print-mod-name-internal modname abbrev t))
	  (let ((params (get-module-parameters arg)))
	    (when (and params (not no-param))
	      (let ((flg nil))
		;; (princ "[")
		(princ "(")
		(dolist (param params)
		  (let ((theory (get-parameter-theory
				 (parameter-theory-module param))))
		    (declare (ignore theory))
		    (if flg (princ ", "))
		    (if (or (null (parameter-context param))
			    (eq arg (parameter-context param)))
			(princ (parameter-arg-name param))
			(progn
			  ;; (format t "~a@" (parameter-arg-name param))
			  (format t "~a." (parameter-arg-name param))
			  (print-mod-name (parameter-context param)
					  stream
					  abbrev
					  t)))
		    ;; patch-begin
		    ;; (princ "::")
		    ;; (print-mod-name theory stream abbrev t)
		    ;; patch-end
		    (setq flg t)))
		;; (princ "]")
		(princ ")")
		))))
	(print-chaos-object arg)
	)))

(defun print-mod-name-internal (val abbrev
				    &optional
				    (no-param nil))
  (declare (values t))
  (if (stringp val)
      (princ val)
      (if (and (consp val) (not (chaos-ast? val)))
	  (if (modexp-is-parameter-theory val)
	      ;; (equal "::" (cadr val))
	      ;; parameter theory
	      (if abbrev
		  (progn
		    (format t "~a" (car val))
		    (princ ".")
		    (print-mod-name (car (last val))
				    *standard-output*
				    abbrev
				    no-param)
		    )
		  ;;
		  (let ((cntxt (fourth val)))
		    (if (and cntxt
			     (not (eq *current-module* cntxt)))
			(progn (format t "~a." (car val))
			       (print-mod-name cntxt *standard-output* t t)
			       (princ " :: "))
			(format t "~a :: " (car val)))
		    (print-mod-name (caddr val) *standard-output* nil t)))
	      (print-chaos-object val))
	  (print-modexp val *standard-output* abbrev no-param))))

(defun print-simple-mod-name (module &optional (stream *standard-output*))
  (if (and *open-module*
	   (equal "%" (get-module-print-name module)))
      (progn
	(princ "%" stream)
	(print-mod-name *open-module* stream t nil))
      (print-mod-name module stream t nil)))

(defun make-module-print-name2 (mod)
  (with-output-to-string (name-string)
    (print-mod-name2 mod name-string t)
    name-string))

(defun print-mod-name2 (arg &optional
			    (stream *standard-output*)
			    (no-param nil))
  (let ((*standard-output* stream))
    (if (module-p arg)
	(let ((modname (get-module-print-name arg)))
	  (if (is-dummy-module arg)
	      (let ((info (getf (module-infos arg) 'rename-mod)))
		(print-mod-name2 (car info) stream no-param)
		(princ "*DUMMY"))
	      (print-mod-name-internal2 modname no-param))
	  (let ((params (get-module-parameters arg)))
	    (when (and params (not no-param))
	      (let ((flg nil))
		(princ "(")
		(dolist (param params)
		  (let ((real-theory (parameter-theory-module param)))
		    (declare (ignore real-theory)) ; ***
		    (if flg (princ ", "))
		    (if (eq arg (parameter-context param))
			(princ (parameter-arg-name param))
			(progn
			  (format t "~a." (parameter-arg-name param))
			  (print-mod-name2 (parameter-context param)
					   stream
					   t)))
		    (setq flg t)))
		(princ ")")
		))))
	;; unknown object ...
	(print-chaos-object arg)
	)))

(defun print-mod-name-internal2 (val &optional (no-param nil))
  (if (stringp val)
      (princ val)
      (if (and (consp val) (not (chaos-ast? val)))
	  (if (equal "::" (cadr val))
	      ;; parameter theory
	      (progn
		(format t "~a." (car val))
		(print-mod-name2 (car (last val))
				 *standard-output*
				 no-param))
	      (print-chaos-object val))
	  (print-modexp val *standard-output* nil no-param))))

(defun get-parameter-theory (mod)
  (cond ((module-p mod)
	 (let ((mod-name (module-name mod)))
	   (cond ((%is-rename mod-name)
		  `(%* ,(get-parameter-theory (%rename-module mod-name))
		       ,(%rename-map mod-name)))
		 ((int-rename-p mod-name)
		  (make-int-rename :module
				   (get-parameter-theory
				    (int-rename-module mod-name))
				   :sort-maps
				   (int-rename-sort-maps mod-name)
				   :op-maps
				   (int-rename-op-maps mod-name)))
		 ((%is-instantiation mod-name)
		  `(%! ,(get-parameter-theory (%instantiation-module mod-name))
		       ,(%instantiation-args mod-name)))
		 ((int-instantiation-p mod-name)
		  (make-int-instantiation :module
					  (get-parameter-theory mod-name)
					  :args
					  (int-instantiation-args mod-name)))
		 ((module-is-parameter-theory mod)
		  (caddr (module-name mod)))
		 (t (with-output-panic-message ()
		      (princ "getting parameter theory, given invalid module.")
		      (print-mod-name mod))))))
	((modexp-is-parameter-theory mod)
	 (caddr mod))
	(t (with-output-panic-message ()
	     (princ "getting parameter theory, given invalid modexp: ")
	     (print-modexp mod)))))

(defun print-parameter-theory-name (mod &optional (stream *standard-output*)
					(abbrev t)
					(no-param t))
  (let ((theory (get-parameter-theory mod)))
    (cond ((module-p theory)
	   (print-mod-name theory stream abbrev no-param))
	  (t (print-modexp theory stream abbrev no-param)))))

;;;-----------------------------------------------------------------------------
;;; SORT
;;;-----------------------------------------------------------------------------

;;; PRINT-SORT-NAME : sort &optional module stream  -> Void
;;; 
(defun print-sort-name (s &optional
			  (module (or *current-module* *last-module*))
			  (stream *standard-output*))
  (unless (sort-struct-p s) (break "print-sort-name: given non sort: ~s" s))
  (let ((*standard-output* stream)
	(mod-name (get-module-print-name (sort-module s))))
    (cond ((and module
		(sort-name-is-ambiguous (sort-id s) module))
	   (if (modexp-is-parameter-theory mod-name)
	       (let ((cntxt (fourth mod-name)))
		 (format t "~a.~a" (string (sort-id s)) (car mod-name))
		 (when (and cntxt (not (eq module cntxt)))
		   (princ ".")
		   (print-mod-name cntxt stream t t)))
	       (progn
		 (format t "~a." (string (sort-id s)))
		 ;; (print-simple-mod-name (sort-module s))
		 (print-mod-name (sort-module s) stream t t))))
	  (t (format t "~a" (string (sort-id s)))))))

(defun sort-print-name (sort &optional (with-mod-qualifier))
  (with-output-to-string (str)
    (let ((*standard-output* str))
      (if with-mod-qualifier
	  (progn
	    (format t "~a" (string (sort-id sort)))
	    (print-simple-mod-name (sort-module sort)))
	(format t "~a" (string (sort-id sort))))
      str)))

;;; PRINT-SORT-LIST
;;;
(defun print-sort-list (lst &optional
			    (module *current-module*)
			    (stream *standard-output*))
  (let ((*standard-output* stream))
    (let ((flag nil))
      (dolist (s lst)
	(print-check)
	(if flag (princ " ") (setq flag t))
	(print-sort-name s module)))))

(defun print-sort-name2 (sort &optional (module *current-module*)
			      (stream *standard-output*))
  (let ((*standard-output* stream)
	(*current-sort-order* (module-sort-order module)))
    (let ((subs (subsorts sort))
	  (supers (supersorts-no-err sort)))
      (when subs
	(print-sort-list subs)
	(print-check)
	(princ " < "))
      (print-sort-name sort)
      (when supers
	(print-check)
	(princ " < ")
	(print-sort-list supers)
	))))
      
;;; PRINT-QUAL-SORT-NAME
;;;
(defun print-qual-sort-name (qs)
  (if (and (consp qs) (eq 'qual (car qs)))
      (let ((nm (cadr qs)) (mod (caddr qs)))
	(if (and (consp nm) (null (cdr nm)))
	    (print-simple-princ (car nm))
	    (print-simple-princ nm))
	(princ ".")
	(if (module-p mod)
	    (print-mod-name mod *standard-output* t t)
	    (print-modexp mod *standard-output* t t)))
      (print-simple-princ-open qs)))

;;;-----------------------------------------------------------------------------
;;; OPERATOR & METHOD
;;;-----------------------------------------------------------------------------

(defun print-qual-op-name (qop)
  (if (and (consp qop) (eq ':qual (car qop)))
      (progn
	(print-simple-princ (cadr qop))
	(princ ".")
	(print-qual-sort-name (caddr qop)))
  (if (consp qop)
      (let ((flag nil))
	(dolist (x qop)
	  (if flag (princ " ") (setq flag t))
	  (if (consp x) (print-qual-sort-name x)
	      (princ x))))
      (print-simple-princ-open qop))))

;;; check if bu strategy: 1 2 3 .. n [ 0 ]
;;; probably would like to improve on this
;;;
(defun print-check-bu (op l)
  (let ((iota (make-list-1-n (operator-num-args op))))
    (or (equal l iota)
	(equal l (append iota '(0))))))

(defun print-check-bu-meth (method l)
  (let ((iota (make-list-1-n (length (method-arity method)))))
    (or (equal l iota)
	(equal l (append iota '(0))))))

(defun print-method-brief (meth)
  (unless (method-p meth)
    (format t "[print-method-brief]: Illegal method given ~a" meth)
    (return-from print-method-brief nil))
  (let* ((*print-indent* (+ 4 *print-indent*))
	 (.file-col. *print-indent*)
	 (is-predicate (method-is-predicate meth)))
    (if is-predicate
	(if (method-is-behavioural meth)
	    (princ "bpred ")
	  (princ "pred "))
      (if (method-is-behavioural meth)
	  (princ "bop ")
	(princ "op ")))
    (print-simple-princ-open (car (method-name meth)))
    (princ " : ")
    (setq .file-col. (1- (file-column *standard-output*)))
    (when (method-arity meth)
      (dolist (ar (method-arity meth))
	(print-sort-name ar *current-module*)
	(princ " ")
	(print-check .file-col. 0)))
    (unless is-predicate
      (princ "-> ")
      (print-sort-name (method-coarity meth) *current-module*))
    (print-check .file-col. 0)
    (print-method-attrs meth)))

;;; PRINT-OP-BRIEF operator
;;;
(defun print-op-brief (op &optional (module *current-module*)
				    (all t)
				    (every nil)
				    (show-context nil))
  (let* ((*print-indent* *print-indent*)
	 (opinfo (get-operator-info op (module-all-operators module)))
	 (methods (if all
		      (opinfo-methods opinfo)
		    (remove-if-not #'(lambda (x)
				       (eq (method-module x)
					   module))
				   (opinfo-methods opinfo)))))
    (dolist (meth (reverse methods))
      (unless (and (not every)
		   (null (method-arity meth))
		   (sort= *sort-id-sort* (method-coarity meth)))
	(when (or (not (method-is-error-method meth))
		  (method-is-user-defined-error-method meth))
	  (print-next)
	  (print-method-brief meth)
	  (when show-context
	    (let ((context-name (get-context-name-extended meth)))
	      (print-next)
	      (format t "-- declared in module ~a" context-name))))))))

;;; PRINT-OP-METH
;;;
(defun print-op-meth (op-meth mod &optional (all t))
  (let ((op (car op-meth))
	(methods (if all
		     (cadr op-meth)
		   (remove-if-not #'(lambda (x)
				      (eq (method-module x) mod))
				  (cadr op-meth)))))
    (if (eq (operator-module op) mod)
	(print-op-brief op mod all)
      (let ((*print-indent* *print-indent*))
	  (dolist (meth methods)
	    (unless (and (not all)
			 (null (method-arity meth))
			 (sort= *sort-id-sort*
				(method-coarity meth)))
	      (print-next)
	      (print-method-brief meth)))))))

(defun print-op-meth2 (op-meth mod &optional (all t))
  (with-in-module (mod)
    (let ((op (car op-meth))
	  (methods (if all
		       (cadr op-meth)
		     (remove-if-not #'(lambda (x)
					(eq (method-module x) mod))
				    (cadr op-meth)))))
      (if (eq (operator-module op) mod)
	  (print-op-brief op mod all)
	  (let ((ind *print-indent*))
	    (dolist (meth methods)
	      (unless (and (null (method-arity meth))
			   (sort= *sort-id-sort*
				  (method-coarity meth)))
		(print-next)
		(let ((*print-indent* (+ 4 ind)))
		  (print-simple-princ-open (operator-symbol op))
		  (print-check)
		  (princ " : ")
		  (when (method-arity meth)
		    (print-sort-list (method-arity meth) mod)
		    (princ " "))
		  (print-check)
		  (princ "-> ")
		  (print-sort-name (method-coarity meth) mod)
		  (print-check)
		  (print-method-attrs meth)
		  ))))))))
  
;;; PRINT-TERM-METHOD : term module stream -> void
;;;
(defun print-term-method (term &optional
			       (module *current-module*)
			       (stream *standard-output*))
  (if (operator-method-p term)
      (print-method term module stream)
      (if (term-is-builtin-constant? term)
	  (print-bi-constant-method term module stream)
	  (print-method (term-head term) module stream))))
  
;;; PRINT-METHOD : method module stream -> void
;;;
(defun print-method (method &optional
			    (module *current-module*)
			    (stream *standard-output*))
  (format stream "~{~a~} : " (method-symbol method))
  (print-sort-list (method-arity method) module stream)
  (princ " -> " stream)
  (print-sort-name (method-coarity method) module stream))
  
;;; METHOD-PRINT-STRING
;;;
(defun method-print-string (meth &optional (module *current-module*))
  (with-output-to-string (str)
    (print-method meth module str)
    str))

;;; PRINT-BI-CONSTANT-METHOD (term &optional module stream)
;;;
(defun print-bi-constant-method (term &optional
				      (module *current-module*)
				      (stream *standard-output*))
  (princ (term-builtin-value term) stream)
  (princ " : -> ")
  (print-sort-name (term-sort term) module stream))
				      

;;; BI-METHOD-PRINT-STRING (term &optional (module *current-module*))
;;;
(defun bi-method-print-string (term &optional (module *current-module*))
  (with-output-to-string (str)
    (print-bi-constant-method term module)))
    

;;; PRINT-OP-ATTRS
;;;-----------------------------------------------------------------------------

(defun print-op-attrs (op)
  ;;  print "attributes" -- for the moment ignore purely syntactic
  ;;  -- i.e. precedence and associativity .
  (let ((strat (let ((val (operator-strategy op)))
		 (if (print-check-bu op val) nil val)))
	(thy (operator-theory op))
	(prec (operator-precedence op)))
    (when (and (eql (car (last strat)) 0)
	       (member 0 (butlast strat)))
      (setq strat (butlast strat)))
    (when (or strat prec (not (eq (theory-info thy) the-e-property)))
      (let ((flag nil)
	    (*print-indent* (1+ *print-indent*)))
	(princ "attr ")
	(print-simple-princ-open (operator-symbol op))
	(princ " { ")
	(when (not (eq (theory-info thy) the-e-property))
	  (setq flag t)
	  (print-theory-brief thy))
	(print-check)
	(when strat
	  (if flag (princ " ") (setq flag t))
	  (princ "strat: ") (print-simple strat))
	(print-check)
	(when prec
	  (if flag (princ " ") (setq flag t))
	  (princ "prec: ") (print-simple prec))
	;; (print-check)
	(princ " }")))))

(defun print-method-attrs (method &optional header)
  (let ((strat (let ((val (method-rewrite-strategy method)))
		 (if (print-check-bu-meth method val) nil val)))
	(constr (method-constructor method))
	(coherent (method-coherent method))
	(thy (method-theory method))
	(prec (or (method-precedence method)
		  (get-method-precedence method)))
	(memo (method-has-memo method))
	(meta-demod (method-is-meta-demod method))
	(assoc (method-associativity method))
	(*print-line-limit* 100))
    (when (and (eql 0 (car (last strat)))
	       (member 0 (butlast strat)))
      (setq strat (butlast strat)))
    (when (or constr coherent
	      strat prec memo meta-demod assoc thy)
      (let ((flag nil)
	    (outstr (make-array '(0) :element-type 'base-char
				:fill-pointer 0 :adjustable t)))
	(with-output-to-string (fs outstr)
	  (let ((*standard-output* fs))
	    (when header (print-next) (princ header))
	    ;; (print-check 0 3)
	    (princ " { ")
	    (setq .file-col. (1- (file-column *standard-output*)))
	    (when (and thy (not (eq (theory-info thy) the-e-property)))
	      (setq flag t)
	      (print-theory-brief thy)
	      (print-check .file-col. 7))
	    (when constr
	      (if flag (princ " ") (setq flag t))
	      (princ "constr")
	      (print-check .file-col. 7))
	    (when coherent
	      (if flag (princ " ") (setq flag t))
	      (princ "coherent")
	      (print-check .file-col. 7))
	    (when strat
	      (if flag (princ " ") (setq flag t))
	      (princ "strat: ") (print-simple strat)
	      (print-check .file-col. 7))
	    (when memo
	      (if flag (princ " ") (setq flag t))
	      (princ "memo")
	      (print-check .file-col. 7))
	    (when meta-demod
	      (if flag (princ " ") (setq flag t))
	      (princ "demod")
	      (print-check .file-col. 7))
	    (when prec
	      (if flag (princ " ") (setq flag t))
	      (princ "prec: ") (print-simple prec)
	      (print-check .file-col. 7))
	    (when assoc
	      ;; (format t "!!~s" assoc)
	      (if flag (princ " ") (setq flag t))
	      (if (eq :left assoc)
		  (princ "l-assoc")
		(princ "r-assoc")))
	    ;; (print-check .file-col.)
	    (princ " }")))
	(print-check 0 (length outstr))
	(princ outstr)))))

;;; AXIOMS, RULES
;;;-----------------------------------------------------------------------------

;;; second parameter is a binding precedence
;;; lower means enclosing operator has stronger binding precedence
;;; 10 none
;;; 8 or   (from IDENTICAL: 59)
;;; 6 xor  (from IDENTICAL: 56)
;;; 4 and  (from IDENTICAL: 55)
;;; 2 not  (from IDENTICAL: 53)
;;; 0 equal/not-equal (from IDENTICAL: 51)

(defun print-id-condition (x stream) (print-id-cond x 10) stream)

(defun print-id-cond (x p &optional (stream *standard-output*))
  (declare (type fixnum p))
  (let ((*standard-output* stream))
    (cond ((eq 'and (car x))
	   (let ((paren (< p 4)))
	     (when paren (princ "("))
	     (print-id-cond-list " and " (cdr x) 4)
	     (when paren (princ ")"))))
	  ((eq 'not-equal (car x))
	   (term-print (cadr x)) (princ " =/== ") (term-print (caddr x)))
	  ((eq 'equal (car x))
	   (term-print (cadr x)) (princ " === ") (term-print (caddr x)))
	  ((eq 'or (car x))
	   (let ((paren (< p 8)))
	     (when paren (princ "("))
	     (print-id-cond-list " or " (cdr x) 8)
	     (when paren (princ ")"))))
	  ((eq 'xor (car x))
	   (let ((paren (< p 6)))
	     (when paren (princ "("))
	     (print-id-cond-list " xor " (cdr x) 6)
	     (when paren (princ ")"))))
	  ((eq 'not (car x))
	   (let ((paren (< p 2)))
	     (when paren (princ "("))
	     (princ "not ")
	     (print-id-cond (cadr x) 2)
	     (when paren (princ ")"))))
	  (t (break "print-id-cond illegal condition"))
	  )))

(defun print-id-cond-list (tok lst r)
  (let ((flag nil))
    (dolist (c lst)
      (if flag (princ tok) (setq flag t))
      (print-id-cond c r))))

(defun print-rule-labels (rul)
  (princ "[")
  (format t "~{~a~^ ~}" (mapcar #'string (axiom-labels rul)))
  (princ "]:")
  )

(defun print-axiom-brief (rul &optional (stream *standard-output*)
					(no-type nil)
					(no-label nil)
					(meta nil))
  (declare (type axiom rul)
	   (type stream stream)
	   (type (or null t) no-type no-label meta))
  (let ((type (axiom-type rul))
	(cnd (not (term-is-similar? *BOOL-true* (axiom-condition rul))))
	(.printed-vars-so-far. nil)
	(*standard-output* stream)
	(axiom-header ""))
    (declare (type symbol type)
	     (type (or t null) cnd)
	     (type list .printed-vars-so-far.)
	     (type string axiom-header))
    (unless no-type
      (case type
	(:equation
	 (if cnd
	     (if (axiom-is-behavioural rul)
		 (if meta
		     (setq axiom-header ":bceq[")
		   (setq axiom-header "bceq "))
	       (if meta
		   (setq axiom-header ":ceq[")
		 (setq axiom-header "ceq ")))
	   (if (axiom-is-behavioural rul)
	       (if meta
		   (setq axiom-header ":beq[")
		 (setq axiom-header "beq "))
	     (if meta
		 (setq axiom-header ":eq[ ")
	       (setq axiom-header "eq ")))))
	(:rule
	 (if cnd
	     (if (axiom-is-behavioural rul)
		 (if meta
		     (setq axiom-header ":bctrans[")
		   (setq axiom-header "bctrans "))
	       (if meta
		   (setq axiom-header ":ctrans[")
		 (setq axiom-header "ctrans ")))
	   (if (axiom-is-behavioural rul)
	       (if meta
		   (setq axiom-header ":btrans[")
		 (setq axiom-header "btrans "))
	     (if meta
		 (setq axiom-header ":trans[")
	       (setq axiom-header "trans ")))))
	(:pignose-axiom
	 (if (axiom-is-behavioural rul)
	     (setq axiom-header "bax ")
	   (setq axiom-header "ax ")))
	(:pignose-goal
	 (if (axiom-is-behavioural rul)
	     (setq axiom-header "bgoal ")
	   (setq axiom-header "goal ")))))
    ;;
    (princ axiom-header)
    (when (and (axiom-labels rul) (not no-label))
      (print-rule-labels rul)
      (princ " "))
    (let ((.file-col. (file-column *standard-output*))
	  (*print-indent* (+ *print-indent* (length axiom-header))))
      ;; LHS
      (princ "(")
      (setq .printed-vars-so-far.
	(term-print (axiom-lhs rul)))
      (princ ")")
      (unless (memq type '(:pignose-axiom :pignose-goal))
	(setq .file-col. (file-column *standard-output*))
	(print-check 0 .file-col.)
	(if (eq type ':rule)
	    (princ " => ")
	  (princ " = "))
	(setq .file-col. (file-column *standard-output*))
	;; RHS
	(term-print (axiom-rhs rul))))
    (let ((.file-col. (file-column *standard-output*)))
      ;; CONDITION
      (when (or cnd
		(and *chaos-verbose* (axiom-id-condition  rul)))
	(print-next)
	(princ "  ")
	(if meta
	    (princ " :if ")
	  (princ " if "))
	(setq .file-col. (+ 4 .file-col.))
	(let ((*print-indent* (+ 5 *print-indent*)))
	  (when cnd
	    (term-print (axiom-condition rul)))
	  (when meta
	    (princ "]"))
	  (when (and *chaos-verbose* (not meta))
	    (when (and cnd (axiom-id-condition rul)) (princ " and "))
	    (when (axiom-id-condition rul)
	      (print-id-condition (axiom-id-condition rul)
				  *standard-output*))))))))

(eval-when (:execute :load-toplevel)
  (setf (symbol-function 'print-rule-brief)
	(symbol-function 'print-axiom-brief))) ; synonim

(defun print-rule-id-inf (x)
  (print-axiom-brief (nth 0 x)) (terpri)
  (print-substitution (nth 1 x))
  (when (cddr x)
    (progn (print-chaos-object (nth 2 x) nil) (terpri))))

(defun print-rule (rul)
  (let ((type (axiom-type rul))
	(cond (not (term-is-similar? *bool-true* (axiom-condition rul))))
	(rul-rhs (axiom-rhs rul))
	(*print-with-sort* t))
    (case type
      (:equation
       (if cond
	   (if (axiom-is-behavioural rul)
	       (princ "- conditional behavioural equation ")
	       (princ "- conditional equation "))
	   (if (axiom-is-behavioural rul)
	       (princ "- behavioural equation ")
	       (princ "- equation "))))
      (:rule
       (if cond
	   (if (axiom-is-behavioural rul)
	       (princ "- conditional behavioural transition ")
	       (princ "- conditional transition "))
	   (if (axiom-is-behavioural rul)
	       (princ "- behavioural transition ")
	       (princ "- transition "))))
      (:pignose-axiom
       (if (axiom-is-behavioural rul)
	   (princ "- behavioural FOPL axiom ")
	 (princ "- FOPL axiom ")))
      (:pignose-goal
       (if (axiom-is-behavioural rul)
	   (princ "- bahvioural FOPL goal ")
	 (princ "- FOPL goal ")))
      )
    (when (axiom-labels rul)
      (print-rule-labels rul)
      (princ " "))
    ;; LHS
    (let ((*print-indent* (+ *print-indent* 2)))
      (print-next)
      (princ "lhs             : ")
      (let ((*print-indent* (+ *print-indent* 4)))
	(term-print (axiom-lhs rul)))
      (print-next)
      ;; RHS
      (princ "rhs             : ")
      (let ((*print-indent* (+ *print-indent* 4)))
	(term-print rul-rhs))
      ;; CONDITION
      (when cond
	(print-next)
	(princ "condition       : ")
	(let ((*print-indent* (+ *print-indent* 4)))
	  (term-print (axiom-condition rul))))
      ;; TOP-OPERATOR/ID CONDITION
      (let ((*print-indent* *print-indent*)
	    (lhs (axiom-lhs rul)))
	;;
	(cond ((term-is-variable? lhs)
	       (print-next)
	       (princ "* lhs is a variable."))
	      (t
	       (let ((head (term-head lhs)))
		 (print-next)
		 (princ "top operator    : ")
		 (when (method-arity head)
		   (print-sort-list (method-arity head) *current-module*)
		   (princ " "))
		 (princ "-> ")
		 (print-sort-name (method-coarity head) *current-module*)))
	      )
	;;
	(when (axiom-id-condition rul)
	  (print-next)
	  (princ "id condition    :  ")
	  (print-id-condition (axiom-id-condition rul)
			      *standard-output*))
	;; KIND
	(when (axiom-kind rul)
	  (print-next)
	  (princ "axiom kind      : ")
	  (case (axiom-kind rul)
	    (:id-theorem (princ "identity"))
	    (:id-completion (princ "id completion"))
	    (:id-ext-theory (princ "extended identity"))
	    (:a-left-theory (princ "left associativity"))
	    (:a-right-theory (princ "right associativity"))
	    (:a-middle-thoery (princ "associativity"))
	    (:ac-theory (princ "associative+commutative"))
	    (:idem-theory (princ "idempotency"))
	    (:bad-rule (princ "illegal as rewrite rule"))
	    (:bad-beh (princ "non coherent beh axiom"))
	    ))
	;; METHOD
	(when (or *on-debug* *chaos-verbose*)
	  (when (axiom-first-match-method rul)
	    (print-next)
	    (princ "* first match  : ")
	    (print-simple (axiom-first-match-method rul)))
	  (when (axiom-next-match-method rul)
	    (print-next)
	    (princ "* next match   : ")
	    (print-simple (axiom-next-match-method rul))))
	;; Extensions
	(let ((exts (axiom-extensions rul)))
	  (when exts
	    (when (and (= (length exts) 1)
		       (not (equal '(nil) exts)))
	      (print-next)
	      (princ "* AC extension: ")
	      (let ((*print-indent* (- *print-indent* 2)))
		(print-rule (car exts))))
	    (when (and (= (length exts) 3)
		       (not (equal exts '(nil nil nil))))
	      (dolist (r exts)
		(print-next)
		(princ "* A extension : ")
		(let ((*print-indent* (- *print-indent* 2)))
		  (print-rule r))))))
	))))

(defun print-axiom (ax) (print-rule ax))

;;; *TODO*
(defun print-rules-detail (mod)
  (let ((rules (module-rules mod)))
    (dolist (r rules)
      (print-chaos-object r) (terpri))
    ))

;;;-----------------------------------------------------------------------------
;;; MODMORPH
;;;-----------------------------------------------------------------------------

(defun print-mapping (mppg &optional (stream *standard-output*))
  (let ((*standard-output* stream)
	(*print-indent* (1+ *print-indent*))
	(*print-array* nil)
	(*print-circle* nil))
    (print-next)
    (princ "name: ")
    (print-modexp (modmorph-name mppg) stream t t)
    (print-next)
    (princ "sort mappings: ")
    (incf *print-indent* 2)
    (dolist (i (modmorph-sort mppg))
      (print-next)
      (format t "~s|~a." (car i) (string (sort-id (car i))))
      (print-modexp (sort-module (car i)))
      (princ "-->")
      (format t "~s|~a." (cdr i) (string (sort-id (cdr i))))
      (print-modexp (sort-module (cdr i)))
      (princ " "))
    (decf *print-indent* 2)
    (print-next)
    (princ "operator mappings : ")
    (incf *print-indent* 2)
    (dolist (i (modmorph-op mppg))
      ;; (method :simple-map . method)
      ;; (method :replacement pvars term)
      (print-next)
      (print-method (car i)) (princ "(")
      (print-mod-name (method-module (car i))
		      *standard-output*
		      t t)
      (princ ")")
      (print-next)
      (princ "--> ")
      (if (eq :simple-map (cadr i))
	  (let ((tm (cdr (last i))))
	    (print-method tm)
	    (princ ":simple-map(")
	    (print-mod-name (method-module tm)
			    *standard-output*
			    t t)
	    (princ ")"))
	  (let ((head (term-head (cadddr i))))
	    (print-method head)
	    (princ ":replacement(")
	    (print-mod-name (method-module head)
			    *standard-output*
			    t t)
	    (princ ")")))
      )
    (decf *print-indent* 2)
    (print-next)
    (princ "module mappings: ")
    (incf *print-indent* 2)
    (dolist (i (modmorph-module mppg))
      (print-next)
      (print-modexp (car i) *standard-output* t t) (princ "-->")
      (print-modexp (cdr i) *standard-output* t t) (princ " "))
    (decf *print-indent* 2)
    ))

;;;-----------------------------------------------------------------------------
;;; RULE-RING
;;;-----------------------------------------------------------------------------

(defun print-rule-ring (rr &optional (stream *standard-output*))
  (princ "rule ring: " stream)
  (do ((rule (initialize-rule-ring rr) (rule-ring-next rr)))
      ;; avoid end-test so can trace it
      ((eq (rule-ring-current rr) (rule-ring-mark rr)))
    (print-axiom-brief rule stream) (print-next 1 stream)
    ))

;;; 
;;; MISC ************************************************************************
;;;

;;; SUBSTITUTION

(defun print-substitution (subst &optional (stream *standard-output*))
  (let ((.file-col. .file-col.))
    (if (or (substitution-is-empty subst)
	    (null (car subst)))
	(princ "{}" stream)
      (let ((s (substitution-list-of-pairs subst)))
	(princ "{ " stream)
	(setq .file-col. (file-column stream))
	(term-print (caar s) stream)
	(print-check .file-col. 0 stream)
	(princ " |-> " stream)
	(term-print (cdar s))
	(dolist (m (cdr s))
	  (princ ", " stream)
	  (print-check .file-col. 0 stream)
	  (let ((src (car m)))
	    (term-print src stream)
	    (print-check .file-col. 0 stream)
	    (princ " |-> " stream)
	    (term-print (cdr m) stream)))
	(princ " }" stream)))))

;;; PARSE DICTIONARY

(defun show-parse-dict (dict)
  (format t "~%Parse Dictionary:")
  (maphash #'(lambda (key val)
	       (format t "~% -- key   = ~s" key)
	       (format t "~%    value = ") (print-chaos-object val))
	   (dictionary-table dict))
  (format t "~% Juxtapositions : ")
  (let ((*print-indent* (+ *print-indent* 2)))
    (dolist (jux (dictionary-juxtaposition dict))
      (print-next)
      (print-chaos-object jux)))
  (format t "~% Builtins = ")
  (print-chaos-object (dictionary-builtins dict)))

(defun print-module-parse-dictionary (mod)
  (with-in-module (mod)
    (show-parse-dict (module-parse-dictionary mod))))

;;; SORT ORDER

(defun pp-sort-order (&optional (sort-order *current-sort-order*))
  (maphash #'(lambda (sort sort-rel)
	       (format t "~%[Sort : ~A](~a)" (sort-print-name sort) sort)
	       (format t "~% Subsorts : ~{ ~A~}(~{ ~a~})"
		       (mapcar #'sort-print-name (_subsorts sort-rel))
		       (_subsorts sort-rel))
	       (format t "~% Supersorts : ~{ ~A~}(~{ ~a~})"
		       (mapcar #'sort-print-name (_supersorts sort-rel))
		       (_supersorts sort-rel))
	       (if (_err-sort sort-rel)
		   (format t "~% Errorsort : ~A(~a)" (sort-print-name
						      (_err-sort sort-rel))
			   (_err-sort sort-rel))))
	   sort-order))

(defun pp-sort-order-raw (module &optional
				 (sort-order (module-sort-order module)))
  (with-in-module (module)
    (maphash #'(lambda (sort sort-rel)
		 (format t "~%[Sort : ~A](~a)" (sort-print-name sort) sort)
		 (format t "~% Subsorts : ~{ ~A~}(~{ ~a~})"
			 (mapcar #'sort-print-name (_subsorts sort-rel))
			 (_subsorts sort-rel))
		 (format t "~% Supersorts : ~{ ~A~}(~{ ~a~})"
			 (mapcar #'sort-print-name (_supersorts sort-rel))
			 (_supersorts sort-rel))
		 (if (_err-sort sort-rel)
		     (format t "~% Errorsort : ~A(~a)" (sort-print-name
							(_err-sort sort-rel))
			     (_err-sort sort-rel))))
	     sort-order)))

;;; MODULE INSTANCE DB

(defun print-instance-db (&optional (module *current-module*))
  (let ((db (module-instance-db module)))
    (unless db
      (format t "~&module ")
      (print-chaos-object module)
      (format t " has no instance database."))
    (format t "~&Contents of instance DB")
    (maphash #'(lambda (key val)
		 (format t "~&---------------------------------")
		 (format t "~&Key = ") (print-chaos-object key)
		 (format t "~&Value = ") (print-chaos-object val))
	     db)))

;;; EOF

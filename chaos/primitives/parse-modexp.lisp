;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: parse-modexp.lisp,v 1.3 2010-06-17 08:23:18 sawada Exp $
(in-package :chaos)
#|==============================================================================
				 System: CHAOS
			       Module: primitives
			    File: parse-modexp.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; Module expression parser for deCafe system.

;;; *****************
;;; MODULE EXPRESSION 
;;;     PARSER        __________________________________________________________
;;; *****************

;;; Syntax *********************************************************************
;;;
;;; ModExpr ::= Identifier | ModExpr "*" RenameMap | ModExpr + ModExpr
;;;           | ModExpr "[" ViewMap "]"
;;;
;;; -- Basic constructors
;;; -- Identifier is also a ModExpr representing simple module name.
;;; [ Identifier < ModExpr ]
;;; op _+_   : ModExpr ModExpr -> ModExpr { constr }
;;; op _*_   : ModExpr RenameMap -> ModExpr { constr }
;;; op _[_]  : ModExpr ViewMap -> ModExpr { constr } --- old syntax
;;; op _(_)  : ModExpr ViewMap -> ModExpr { constr } --- new syntax
;;;
;;; -- attributes :
;;; --   precedence: _[] > _*_ > _+_
;;; --   all are left associative.
;;; attr _+_ { assoc comm idem l-assoc prec: 3 }
;;; attr _*_ { l-assoc prec: 2 }
;;; attr _[_] { l-assoc prec: 1 }
;;; attr _(_) { l-assoc prec: 1 }
;;;
;;; -- Map
;;; [ Map, 
;;;   SortMap OpMap PramMap VarDecl < MapElt ]
;;; op {_}   : MapElt -> MapSeq
;;; op sort_->_ : Identifier Identifier -> SortMap
;;; op hsort_->_ : Identifier Identifier -> SortMap
;;; op op_->_ : Identifier Identifier -> OpMap
;;; op op_->_ : Term Term -> OpMap
;;; op param_->_ : Identifier Identifier -> ParamMap
;;; op var_ : VarForm -> VarDecl
;;; op bop_->_ : Identifier Identifier -> OpMap
;;; op bop_->_ : Term Term -> OpMap
;;;

;;; 	     *** Changes in module expression syntax ***
;;;                 Mon May 19 15:45:41 JST 1997
;;; due to the discussion held at JAIST in the late March of '97,
;;; the syntax is changed.
;;; (1) the instantiation operator is defined as
;;;         op _(_) : ModExpr ViewMap -> ModExpr { constr }
;;;     now it is heavilly overloaded with meta-parens.
;;; (2) maps allow additional  keywords
;;;     1 `hsort' for specifying map between hidden sorts and
;;;     2 `bop' for behavioural operator mappings.
;;;
;;;*****************************************************************************

;;; 				**** READER ****
;;;                      now defined in comlib/reader.lisp

;;; 				**** PARSER ****
;;;=============================================================================

;;;-----------------------------------------------------------------------------
;;; PARSE-MODEXP : list[Token] -> ModuleExpression
;;;
;;; a bottom up parser of Chaos Module Expression.
;;; global: *modexp-parse-input* binds whole module expression to be parsed.
;;;-----------------------------------------------------------------------------

(defun parse-modexp (inp)
  (declare (type (or simple-string list) inp))
  (when (stringp inp)
    (setf inp (read-modexp-from-string inp)))
  (unless inp
    (with-output-chaos-error ('empty-modexp)
      (princ "module expression is empty.")
      ))
  (when (atom inp)
    (setf inp (list inp)))
  (let ((*modexp-parse-input* inp))
    (prog1
	(do-parse-modexp)
      (when *modexp-parse-input*
	(with-output-chaos-error ('invalid-modexp)
	  (format t "invalid module expression: ~a" inp)
	  (print-next)
	  (format t "remaining ~a" *modexp-parse-input*)))))
  )

;;; DO-PARSE-MODEXP : {*modexp-parse-input*} ->
;;;                   {*modexp-parse-input*} ModuleExpression
;;;
(defun do-parse-modexp ()
  ;; NOTE: precedence [] > * > +
  ;;
  (let ((e1 (parse-rename-or-inst)))
    (if (null *modexp-parse-input*)
	;; the whole expression is parsed by `parse-rename-or-inst'.
	e1
	(case-equal (car *modexp-parse-input*)
	  ;; parse remainders
	  ("+" (let ((args (list e1)))
		 (loop (modexp-skip)	; skip "+"
					; collect "+" arguments.
		       (push (parse-rename-or-inst) args)
		       (when (or (null *modexp-parse-input*)
				 (not (equal "+" (car *modexp-parse-input*))))
			 ;; whole modexpr is parsed, or other types comes.
			 (return)))
		 (%plus* (reverse args))))
	  ;; the following tokens can terminate one module expr.
	  (("]" "," ")" "{" "to" "->" "}") e1)
	  (t (with-output-chaos-error ('invlaid-modexp)
	       (princ "error in module expression: ")
	       (print-chaos-object e1)
	       (format t " is followed by ~a.~%" (car *modexp-parse-input*))
	       ))))))

;;; PARSING ROUTINES FOR EACH SYNTACTIC CLASS.__________________________________

;;; PARSE-RENAME-OR-INST
;;;-----------------------------------------------------------------------------
(defun parse-rename-or-inst ()
  ;; NOTE : the predence of instantiation is higher than rename .
  ;; first we try to parse instantiation.
  (let ((e1 (parse-instantiation)))
    (if (null *modexp-parse-input*)
	;; the whole expression is parsed by `parse-instantiation'.
	e1
	;; e1 may be an instantiation or of other types of module expressions.
	(case-equal (car *modexp-parse-input*)
	  ("*"				; Rename.
	   ;; gather renaming operations in left associative manner.
	   (loop (modexp-skip)		; skip "*"
		 (setq e1 (%rename* e1 (parse-map-body)))
		 (when (or (null *modexp-parse-input*)
			   (not (equal "*" (car *modexp-parse-input*))))
		   ;; all are parsed or other type of ModExpr comes.
		   (return e1))))

	  ;; the following tokens terminate rename or other preceding module expressions,
	  ;; thus we return it as is.
	  (("]" "," ")" "{" "to" "->" "::" "+" "}")  e1) ; "with" "and" ...??

	  ;; otherwise we encounter an error.
	  (t (with-output-chaos-error ('invalid-modexp)
	       (princ "module expression: ")
	       (print-chaos-object e1)
	       (format t " is followed by ~a.~%" (car *modexp-parse-input*))
	       ))))))

;;; PARSE-MAP-BODY
;;; gather mapping.
;;; 
;;;-----------------------------------------------------------------------------
(defun parse-map-body (&optional (type :rename))
  (declare (type symbol type))
  (cond ((null *modexp-parse-input*)
	 (with-output-chaos-error ('invalid-modexp)
	   (princ "premature end of module expression in a mapping.")
	   ))
	;; the first token of rename must be "{".
	((not (equal "{" (car *modexp-parse-input*)))
	 (with-output-chaos-error ('invalid-modexp)
	   (princ "body of renaming should be preceded by \"{\"")
	   ))
	(t (modexp-skip)		; skip "{"
	   (let ((sort-map nil)		; accumulators
		 (hsort-map nil)
		 (op-map nil)
		 (bop-map nil)
		 (vars nil)
		 (param-map nil)
		 (map nil))
	     ;; gather rename map elements
	     (loop (when (null *modexp-parse-input*)
		     (with-output-chaos-error ('invalid-modexp)
		       (princ "ill-formed mapping.")
		       ))
		   (setq map (if (eq type :rename)
				 (parse-map-elt)
				 (parse-view-elt)))
		   (case (car map)
		     (:sort (push (cdr map) sort-map))
		     (:hsort (push (cdr map) hsort-map))
		     (:op (push (cdr map) op-map))
		     (:bop (push (cdr map) bop-map))
		     (:var (push (cdr map) vars)) ; only for case view map
		     (:param (push (cdr map) param-map)) ; only for case rename map
					; *note* not implemented yet though.
		     (t nil))		; empty case
		   ;; "}" terminates rename map.
		   (when (equal "}" (car *modexp-parse-input*))
		     (modexp-skip)	; consume "}"
		     (return))		; then return
		   ;; we just ignore ",", a unnecessary separator of renaming.
		   (when (equal "," (car *modexp-parse-input*))
		     (modexp-skip)))
	     (%rmap* (nconc (when sort-map (list (%ren-sort* sort-map)))
			    (when hsort-map (list (%ren-hsort* hsort-map)))
			    (when op-map (list (%ren-op* op-map)))
			    (when bop-map (list (%ren-bop* bop-map)))
			    (when vars (list (%vars* vars)))
			    (when param-map (list (%ren-param* param-map)))))
	     ))))

;;; PARSE-MAP-ELT 
;;; parse one map element.
;;; returns (<kind> from to)
;;;  <kind> ::= :sort | :op | :param | :hsort | :bop
;;;
(defun parse-map-elt ()
  (cond ((null *modexp-parse-input*)
	 (with-output-chaos-error ('invalid-modexp)
	   (princ "premature end of map elements.")
	   ))
	(t (case-equal (car *modexp-parse-input*)
	     ("sort"		; sort map
	      (let (from to)
		(modexp-skip)	; skip "sort"
		;; "->" separates from\to
		(setq from (parse-sort-reference '("->")))
		(when (not (equal "->" (car *modexp-parse-input*)))
		  (with-output-chaos-error ('invalid-modexp)
		    (format t "parsing sort mapping of ~a, missing \"->\"" 
			    from)
		    ))
		(modexp-skip)	; skip "->"
		;; parse `to' part.
		(setq to (parse-sort-reference '("," "}" "]")))
		(list :sort from to)))
	     ("hsort"		; hidden sort map
	      (let (from to)
		(modexp-skip)	; skip "hsort"
		;; "->" separates from & to
		(setq from (parse-sort-reference '("->")))
		(when (not (equal "->" (car *modexp-parse-input*)))
		  (with-output-chaos-error ('invalid-modexp)
		    (format t "parsing hidden sort mapping of ~a, missing \"->\"" 
			    from)
		    ))
		(modexp-skip)	; skip "->"
		;; parse `to' part.
		(setq to (parse-sort-reference '("," "}" "]")))
		(list :hsort from to)))
	     ("op"			; operator renaming
	      (let (from to)
		(modexp-skip)		; skip "op"
		(setq from (parse-operator-reference '("->")))
		(when (not (equal "->" (car *modexp-parse-input*)))
		  (with-output-chaos-error ('invalid-modexp)
		    (format t "parsing operator mapping of ~a, missing \"->\""
			    from)
		    ))
		(modexp-skip)		; skip "->"
		(setq to (parse-operator-reference '("," "}" "]")))
		(list :op from to)))
	     ("bop"			; behavioural operator renaming
	      (let (from to)
		(modexp-skip)		; skip "bop"
		(setq from (parse-operator-reference '("->")))
		(when (not (equal "->" (car *modexp-parse-input*)))
		  (with-output-chaos-error ('invalid-modexp)
		    (format t "parsing behavioural operator mapping of ~a, missing \"->\""
			    from)
		    ))
		(modexp-skip)		; skip "->"
		(setq to (parse-operator-reference '("," "}" "]")))
		(list :bop from to)))
	     ("param"			; parameter mapping.
					; can parse but NOT really implemented. ****
	      (let (from to)
		(modexp-skip)		; skip "param"
		(setq from (modexp-parse-param-specn '("->")))
		(when (not (equal "->" (car *modexp-parse-input*)))
		  (with-output-chaos-error ('invalid-modexp)
		    (format t "parsing parameter mapping of ~a, missing \"->\""
			    from)
		    ))
		(modexp-skip)		; skip "->"
		(setq to (modexp-parse-param-specn '("," "}" "]")))
		(list :param from to)))
	     ("}"			; emtpy map
	      nil)
	     (t (with-output-chaos-error ('invalid-modexp)
		  (format t "expecting \"sort\",\"hsort\",\"op\" or \"bop\", encounterd ~a."
			  (car *modexp-parse-input*))
		  )))
	   )))

;;; PARSE-INSTATIATION
;;; parse a modexpr, then try to parse the first of the rest as instantiation,
;;; if it is not an instantiation, returns the parsed modexpr.
;;;-----------------------------------------------------------------------------
(defun parse-instantiation ()
  (labels ((token-is-not-instantiation (token)
	     (declare (type simple-string token))
	     (dotimes (i (length token) t)
	       (declare (type fixnum i))
	       (let ((ch (schar token i)))
		 (declare (type character ch))
		 (when (member ch '(#\[ #\] #\( #\)))
		   (return nil)))))
	   (parse-basic ()
	     ;; * assumes Modexpr which can be an argument of any type
	     ;;   of module expressions other than instantiation, or can be a
	     ;;   simple name. 
	     (cond ((equal "(" (car *modexp-parse-input*))
		    (modexp-skip)
		    (let ((m (do-parse-modexp)))
		      (cond ((equal ")" (car *modexp-parse-input*))
			     (modexp-skip)
			     m)
			    (t (with-output-msg ()
				 (princ "unmatched \"(\" in module expression after ")
				 (print-next)
				 (print-modexp m)
				 (chaos-error 'invalid-modexp) )))))
		   ((token-is-not-instantiation (car *modexp-parse-input*))
		    (prog1 (car *modexp-parse-input*) (modexp-skip)))
		   (t (with-output-chaos-error ('invalid-modexp)
			(princ (car *modexp-parse-input*))
			(print "doesn't make sense in module expression.")
			)))))
    (let ((m (parse-basic)))
      (cond ((null *modexp-parse-input*) m) ; was just a simple name or parenced
					    ; modexpr.
	    ((member (car *modexp-parse-input*)
		     '("[" "(") :test #'equal)
	     ;; instantiation!, its first argument is now bound to `m'.
	     (modexp-skip)		; skip "[" ("(")
	     (let ((args (modexp-parse-args)))
					; parse second arg, i.e., the view.
	       ;; view must be ended with "]".
	       (when (not (member (car *modexp-parse-input*)
				  '("]" ")") :test #'equal))
		 (with-output-chaos-error ('invalid-modexp)
		   (princ "\"[\" appears without matching \"]\" in instantiation.")
		    ))
	       (modexp-skip)		; skip "]" (")").
	       (%instantiation* m args)))
	    ;; the *modexp-parse-input* was a module expression any other than
	    ;; instantiation. which is either a simple name or a parenced modexpr,
	    ;; and it can be an argument of the following operator or it just a
	    ;; simple name.
	    (t
	     m)))))

;;; MODEXP-PARSE-ARGS
;;; called by `parse-instantiation'; parses arguments to parameterized module.
;;; * assumption *
;;;   we have just encountered "[" which begins a seq of arguments, and
;;;   the first elt of *modexp-parse-input* is pointing a token just after "[".
;;;
(declaim (special *positional-arg-pos* *arg-type*))
(declaim (type fixnum *positional-arg-pos*))
(defvar *positional-arg-pos* 0)
(defvar *arg-type* nil)

(defun modexp-parse-args ()
  (let ((*positional-arg-pos* 0)
	(*arg-type* nil))
    (cond ((null *modexp-parse-input*)
	   (with-output-chaos-error ('invalid-modexp)
	     (princ "parsing instantiation, premature end of input in argument list.")
	      ))
	  ((member (car *modexp-parse-input*) '("]" ")") :test #'equal)
	   nil)				; empty arugment.
	  ;; accumulate arguments.
	  (t (let ((res nil)
		   (arg nil))
	       (loop (setf arg (modexp-parse-arg))
		     (when arg
		       (setq res (cons arg res))
		       (incf *positional-arg-pos*))
		     ;; "]" teminates arguments.
		     (when (member (car *modexp-parse-input*) '("]" ")") :test #'equal)
		       (return (nreverse res)))
		     ;; skip "," as a separator of each argument.
		     (when (equal "," (car *modexp-parse-input*))
		       (modexp-skip))))
	     ))))

(defun parse-instantiate-arg-name (name)
  (declare (type simple-string name))
  (let ((pos (position #\@ name)))
    (if pos				; indirect argument ref.
	(cons (subseq name 0 pos)
	      (subseq name (1+ pos)))
	(cons name nil))))

(defun modexp-parse-arg ()
  (when (null *modexp-parse-input*)
    (with-output-chaos-error ('invalid-modexp)
      (princ "premature end of input in argument of parameterized module.")
      ))
  ;;
  (let ((arg-name (car *modexp-parse-input*)))
    (modexp-skip)			; move to next token
    ;; try to parse formal argument name.
    ;;  - it can be omitted, in this case we are parsing positional arguments,
    ;;;   and `arg-name' should bind a real argument, i.e., a view.
    ;;  - otherwise normal keyword type argument passing is processed.
    ;;    in this case, arg-name should bind formal argument name.
    (if (equal "<=" (car *modexp-parse-input*))
	(progn
	  (unless (or (eq *arg-type* ':key) (null *arg-type*))
	    (with-output-chaos-error ('invalid-modexp)
	      (princ "you can not use both positional and keyword type argument in a combined manner.")
	       ))
	  (modexp-skip)			; skip "<="
	  (setq arg-name (parse-instantiate-arg-name arg-name))
	  (setq *arg-type* ':key))
	(progn
	  (unless (or (eq *arg-type* ':pos) (null *arg-type*))
	    (with-output-chaos-error ('invalid-modexp)
	      (princ "you cannot use both positional and keyword type argument in a combined manner.")
	      ))
	  (setq *arg-type* ':pos)
	  (push arg-name *modexp-parse-input*) ; restore view 
	  (setq arg-name *positional-arg-pos*) ; should we set keyword name
					       ; here? 
	  
	  ))
    ;; parse actual argument, i.e., view.
    (cond ((equal "view" (car *modexp-parse-input*)) ; explicit view argument.
	   (%!arg* arg-name (do-parse-view)))
	  ((equal "{" (car *modexp-parse-input*)) ; given map directly.
	   ;; both `from' & `to' is omitted...
	   (let (view)			; the resulting view
	     (setq view (%view* 'none 'none (parse-view-body)))
					; was parse-map-body
	     (%!arg* arg-name view)))
	  ;; normal? argument
	  (t (let ((mod (do-parse-modexp)) ; either a name of declared view or
					   ; a modexpr.
		   (view nil))
	       ;;
	       (cond ((equal "{" (car *modexp-parse-input*)) ; the map is given
		      ;; this case mod must be a modexpr other than view name.
		      (setq view (%view* 'none mod (parse-view-body)))
					; was parse-map-body
		      (%!arg* arg-name view))
		     ;; NO map is given.................
		     (t (setq view (%view* 'none
					   (make-?-name mod)
					   nil))
			(%!arg* arg-name view))))))
    ))

;;;-----------------------------------------------------------------------------
;;; PARSE-VIEW : list[Token] ->  ModuleExpression
;;; global: *modexp-parse-input* binds whole modexpr to be parsed.
;;; Try to parse view declaration form.
;;;-----------------------------------------------------------------------------

(defun parse-view (form)
  (declare (type list form))
  (let ((*modexp-parse-input* form))
    (do-parse-view)))

;;; DO-PARSE-VIEW
;;; parse view declaration.
;;; also used for parsing argument of instantiation.
;;;
(defun do-parse-view ()
  (cond ((equal "view" (car *modexp-parse-input*))
	 (modexp-skip)			; skip "view"
	 (let ((from 'none)		; theory
	       (to nil)			; target module
	       (mapping nil))		; mapping

	   ;; parse theory module part if specified
	   (when (equal "from" (car *modexp-parse-input*))
	     (modexp-skip)		; skip "from"
	     ;; theory module can be an arbitrary module expression.
	     (setq from (do-parse-modexp)))
	   ;; we always require target module
	   (when (not (equal "to" (car *modexp-parse-input*)))
	     (with-output-chaos-error ('invalid-modexp)
	       (format t "expecting \"to\" in view, but encountered ~A"
		       (car *modexp-parse-input*))
	       ))
	   (modexp-skip)		; skip "to"
	   ;; parse target module expression
	   (setq to (do-parse-modexp))
	   ;; parse mapping
	   (setq mapping (parse-view-body)) ; was parse-map-body...
	   ;;
	   (%view* from to mapping)))
	(t (with-output-chaos-error ('invalid-modexp)
	     (princ "in view, not expecting ")
	     (princ (car *modexp-parse-input*))
	      ))))

;;; PARSE-VIEW-BODY
;;; similar to `parse-map-body' but allows variable declaration and
;;; specifying operator maps by terms.
;;;
(defun parse-view-body () (parse-map-body :view))

;;; PARSE-VIEW-ELT
;;; 
(defun parse-view-elt ()
  (flet ((parse-op-name (cntxt)
	   (declare (type list cntxt))
	   (let ((res nil))
	     (loop (when (null *modexp-parse-input*)
		     (with-output-chaos-error ('invalid-modexp)
		       (princ "premature end of input in operator pattern:")
		       (print-next)
		       (format t "beginning of pattern: ~{~s~}" (nreverse res))
		        ))
		   (when (member (car *modexp-parse-input*) cntxt :test #'equal)
		     (return))
		   (setq res (nconc res (parse-balanced-context cntxt))))
	     res )))
    (cond ((null *modexp-parse-input*)
	   (with-output-chaos-error ('invalid-modexp)
	     (princ "premature end of view body")
	      ))
	  (t (case-equal (car *modexp-parse-input*)
		("sort"			; sort map
		 (let (from to)
		   (modexp-skip)	; skip "sort"
		   ;; "->" separates from & to
		   (setq from (parse-sort-reference '("->")))
		   (when (not (equal "->" (car *modexp-parse-input*)))
		     (with-output-chaos-error ('invalid-modexp)
		       (format t "parsing sort mapping of ~a, missing \"->\"" 
			       from)
		       ))
		   (modexp-skip)	; skip "->"
		   ;; parse `to' part.
		   (setq to (parse-sort-reference '("," "}" "]")))
		   `(:sort ,from ,to)))
		("hsort"		; hidden sort map
		 (let (from to)
		   (modexp-skip)	; skip "hsort"
		   ;; "->" separates from & to
		   (setq from (parse-sort-reference '("->")))
		   (when (not (equal "->" (car *modexp-parse-input*)))
		     (with-output-chaos-error ('invalid-modexp)
		       (format t "parsing hidden sort mapping of ~a, missing \"->\"" 
			       from)
		       ))
		   (modexp-skip)	; skip "->"
		   ;; parse `to' part.
		   (setq to (parse-sort-reference '("," "}" "]")))
		   `(:hsort ,from ,to)))
		(("var" "vars")
		 (let (v s)
		   (modexp-skip)		; skip "var", "vars"
		   (setq v nil)
		   (loop (let ((inp (car *modexp-parse-input*)))
			   (when (equal ":" inp) (return))
			   (push inp v)
			   (modexp-skip)))
		   (modexp-skip)
		   (setq s (parse-sort-reference '("," "}" "." "]")))
		   `(:var ,v ,s)))
		("op"			; operator map
		 (let (a b)
		   (modexp-skip)		; skip "op"
		   (setq a (parse-op-name '("->")))
		   (when (not (equal "->" (car *modexp-parse-input*)))
		     (with-output-chaos-error ('invalid-modexp)
		       (format t "in view body, for op ~a,  missing \"->\"" a)
		       ))
		   (modexp-skip)
		   (setq b (parse-op-name '("." "}" ",")))
		   `(:op ,a ,b)))
		("bop"			; behavioural operator map
		 (let (a b)
		   (modexp-skip)		; skip "bop"
		   (setq a (parse-op-name '("->")))
		   (when (not (equal "->" (car *modexp-parse-input*)))
		     (with-output-chaos-error ('invalid-modexp)
		       (format t "in view body, for bop ~a, missing \"->\"" a)
		       ))
		   (modexp-skip)
		   (setq b (parse-op-name '("." "}" ",")))
		   `(:bop ,a ,b)))
		("}"			; empty body
		 nil)
		(t (with-output-chaos-error ('invalid-modexp)
		     (format t "in view mapping, expecting \"sort\", \"hsort\", \"op\", \"bop\" or \"var\", but encoutered ~A."
			     (car *modexp-parse-input*))
		     )))
	     ))))

;;; *************************
;;; PARSE SORT REFERENCE FORM___________________________________________________
;;; *************************

;;; PARSE-SORT-REFERENCE
;;; a sort reference parser.
;;;
(defun parse-sort-reference (cntxt)
  (declare (type list cntxt))
  (unless *modexp-parse-input*
    (with-output-chaos-error ('invalid-modexp)
      (princ "premature end of input at sort specification.")
      ))
  (do-parse-sort-ref cntxt))

#||
;;; MODEXP-CHECK-QUAL
(defun modexp-check-qual (x)
  (if (stringp x)
      (let ((pos (position #\. x)))
	(if (and pos (< 0 pos) (< (1+ pos) (length x)))
	    `(:qual ,(list (subseq x 0 pos))
	           ,(subseq x (1+ pos)))
	    x))
      x))
||#

;;; DO-PARSE-SORT-REF
;;; * NOTE *
;;; Because sort reference can have qualifier, we need to parse module expression.
;;; The situation is mutually recursive, i.e., module expression (or view) may
;;; have sort reference in it.
;;; Thus the following code also used for parsing module expressions and views.
;;;
;;; <SortRef> ::= Identifier | Idetifier.<ModExpr> | ( Identifier . <ModexPr> )
;;;
(defun do-parse-sort-ref (cntxt)
  (declare (type list cntxt))
  (cond ((equal "(" (car *modexp-parse-input*))
	 ;; parenthesized reference
	 (modexp-skip)			; skip "("
	 ;; get first one token
	 (let ((val (parse-balanced-context-one ")"))
	       (flag t))		; t iff we are in parenthesized units.
	   (when (equal ")" (car *modexp-parse-input*))
	     (modexp-skip)		; skip ")"
	     (setq flag nil))		; we are no more in parenthe
	   ;; consider the rest.
	   (let ((res (cond ((and (equal "." (car *modexp-parse-input*))
				  (not (member "." cntxt :test #'equal)))
			     ;; ( <sort-ref> . <ModExpr> ) ---------------------
			     (modexp-skip) ; skip "."
			     (%sort-ref* (car val) (do-parse-modexp)))
			    ((and (null (cdr val))
				  (stringp (car val))
				  (eql #\. (char (the simple-string (car val))
						 (1- (length (the simple-string
							       (car val)))))))
			     ;; ( "sort-name." ... ) --------------------------
			     (%sort-ref* (subseq (the simple-string (car val))
						 0
						 (1- (length
						      (the simple-string (car val)))))
					 (do-parse-modexp)))
			    ((and *modexp-parse-input*
				  (<= 2 (length
					 (the simple-string
					   (car *modexp-parse-input*))))
				  (eql #\. (char (the simple-string
						   (car *modexp-parse-input*))
						 0)))
			     ;; ( <sort-ref> ".foo" ... ) ---------------------
			     (let ((name (car *modexp-parse-input*)))
			       (declare (type simple-string name))
			       (modexp-skip)
			       (%sort-ref* (car val) (subseq name 1))))
			    ;; ( <sort-ref> ) ---------------------------------
			    (t (%sort-ref* (car val))))))
	     (when flag
	       (unless (equal ")" (car *modexp-parse-input*))
		 (with-output-chaos-error ('invalid-modexp)
		   (princ "unbalanced parentheses in sort specification.")
		   (print-next)
		   (princ "context: ")
		   (print-simple-princ-open val)
		   ))
	       (modexp-skip))
	     res)))
	;;
	;; not parenthesized reference
	;;
	(t (let ((val (car *modexp-parse-input*)))
	     (modexp-skip)		; skip one token
	     (if (stringp val)
		 ;; 
		 (if (eql #\. (char (the simple-string val) (1- (length val))))
		     ;; the last character is ".", thus we assume the rest is
		     ;; a modexp which qualifies the name.
		     (%sort-ref* (subseq (the simple-string val)
					 0 (1- (length val))) ; name
				 (do-parse-modexp)) ; quilifier 
		     (let ((pos (position #\. (the simple-string val))))
		       (if pos		; name is quilified by simple modexpr.
			   (%sort-ref* (subseq (the simple-string val) 0 pos)
				       (subseq (the simple-string val) (1+ pos)))
			   (%sort-ref* val))))
		 ;; return it as is.
		 (%sort-ref* val)
		 )))))

;;; ****************************
;;; PARSE OPERATOR REFRENCE FORM______________________________________________________
;;; ****************************

;;; PARSE-OPERATOR-REFERENCE
;;; used in renames and after op in parameter position
;;;
(defun parse-operator-reference (cntxt)
  (declare (type list cntxt))
  (when *on-modexp-debug*
    (format t "~&[parse-operator-reference]:*modexp-parse-input*=~a" *modexp-parse-input*))
  (cond ((null *modexp-parse-input*)
	 (with-output-chaos-error ('invalid-modexp)
	   (princ "premature end of input at operator specification")
	   ))
	((equal "(" (car *modexp-parse-input*))
	 ;; parenthesized reference -------------------------------------------------
	 (modexp-skip)			; skip "("
	 (let ((val (parse-op-simple-name '(")")))
	       (flag t))
	   (when (equal ")" (car *modexp-parse-input*))
	     (modexp-skip)
	     (setq flag nil))		; we are now out of parens.
	   ;;
	   (let ((res (cond ((and (equal "." (car *modexp-parse-input*))
				  (not (member "." cntxt :test #'equal)))
			     ;; ( <simple-op-ref> . <Modexpr> ...)
			     (modexp-skip) ; skip "."
			     (%opref* val (do-parse-modexp)))
			    ((and *modexp-parse-input*
				  (<= 2 (length (car *modexp-parse-input*)))
				  (eql #\. (char
					    (the simple-string
					      (car *modexp-parse-input*))
					    0)))
			     ;; ( <simple-op-ref> ".foo" .. )
			     (let ((name (car *modexp-parse-input*)))
			       (declare (type simple-string name))
			       (modexp-skip) ; consume one token
			       (%opref* val (subseq name 1))))
			    ;; as is 
			    (t (%opref* val)))))
	     (when flag
	       (unless (equal ")" (car *modexp-parse-input*))
		 (with-output-chaos-error ('invalid-modexp)
		   (princ "unbalanced parentheses in operator specification.")
		   (print-next)
		   (princ "context: ")
		   (print-simple-princ-open val)
		   ))
	       (modexp-skip))
	     res)))
	;; not in parenthe ---------------------------------------------------------
	(t (let ((val (parse-op-simple-name cntxt)))
	     (if (and (consp val) (null (cdr val)) (stringp (car val)))
		 ;; op-ref is just a simple string.
		 (let ((name (car val)))
		   (declare (type simple-string name))
		   (let ((pos (position #\. name)))
		     (if (and pos (< 0 pos) (< (1+ pos) (length name)))
			 ;; "foo.qualifier"
			 (%opref* (list (subseq name 0 pos))
				  (subseq name (1+ pos)))
			 (%opref* val))))
		 (%opref* val)))))
  )

;;; PARSE-OP-SIMPLE-NAME

(defun parse-op-simple-name (cntxt)
  (if (equal "(" (car *modexp-parse-input*))
      (progn (modexp-skip)
	     (prog1
		 (parse-balanced-context '(")"))
	       (modexp-skip)))
      (let ((res nil))
	(loop (when (null *modexp-parse-input*)
		(if (null cntxt)
		    (return)
		  (with-output-chaos-error ('invalid-modexp)
		    (princ "premature end of input in operator pattern.")
		    (print-next)
		    (princ "beginning of pattern: ")
		    (print-simple-princ-open (nreverse res))
		    (print-next)
		    (princ "expecting one of: ")
		    (princ cntxt)
		    )))
	  (when (member (car *modexp-parse-input*) cntxt :test #'equal)
	    (return))
	      (setq res (nconc res (parse-balanced-context cntxt))))
	res)))

;;; PARSE PARAMETER REFERENCE
;;;*****************************************************************************

;;; MODEXP-PARSE-PARAM-SPECN
(defun modexp-parse-param-specn (cntxt)
  (declare (type list cntxt))
  (if (equal "(" (car *modexp-parse-input*))
      (progn (modexp-skip)
	     (prog1
		 (parse-balanced-context '(")"))
	       (modexp-skip)))
      (let ((res nil))
	(loop (when (null *modexp-parse-input*)
		(if (null cntxt)
		    (return)
		    (with-output-chaos-error ('invalid-modexp)
		      (princ "premature end of input in parameter name.")
		      (print-next)
		      (princ "beginning of pattern: ")
		      (print-simple-princ-open (nreverse res))
		      (print-next)
		      (princ "expecting one of: ")
		      (princ cntxt)
		      )))
	      (when (member (car *modexp-parse-input*) cntxt :test #'equal)
		(return))
	      (setq res (nconc res (parse-balanced-context cntxt))))
	res)))


;;; PARSE-BALANCED-CONTEXT

(defun parse-balanced-context (cntxt)
  (declare (type list cntxt))
  (let ((res nil)
	(d 0))
    (declare (type fixnum d))
    (loop (cond ((null *modexp-parse-input*)
		 (if (null cntxt)
		     (return (nreverse res))
		     (with-output-chaos-error ('invalid-modexp)
		       (princ "premature end of input after:")
		       (print-simple-princ-open (nreverse res))
		       )))
		(t (let ((cur (car *modexp-parse-input*)))
		     (when (and (and (= 0 d)
				     (member cur cntxt :test #'equal)))
		       (return (nreverse res)))
		     (setq res (cons cur res))
		     (modexp-skip)
		     (cond ((equal ")" cur)
			    (decf d)
			    (when (= -1 d)
			      (with-output-simple-msg ()
				(princ "[Error] too many ')'s") 
				(return (nreverse res)))))
			   ((equal "(" cur) (incf d)))))))))

;;; PARSE-BALANCED-CONTEXT-ONE

(defun parse-balanced-context-one (cntxt)
  (declare (ignore cntxt))
  (if (equal "(" (car *modexp-parse-input*))
      (progn (modexp-skip)
	     (prog1
		 (parse-balanced-context '(")"))
	       (modexp-skip)))
      (prog1
	  (list (car *modexp-parse-input*))
	(modexp-skip))
      ))

;;; EOF

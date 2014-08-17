;;;-*-Mode:LISP; Package: CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: parse-engine.lisp,v 1.12 2010-07-20 06:59:37 sawada Exp $
(in-package :chaos)
#|==============================================================================
				  System:Chaos
			   Module:term-parser.chaos
			    File: parse-engine.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; *NOTE* PARSING ALGORITHM is BASED ON OBJ3 interpreter of SRI International.
;;; Copyright 1988,1991 SRI International.

;;;*********************************
;;; PARSE DICTIONARY BASIC ROUTINES
;;;*********************************

;;; DICTIONARY-ADD-INFO-ON-TOKEN : Dictionary Token Value -> {Dictionary}
;;;
(defun dictionary-add-info-on-token (dictionary token value)
  (declare (type parse-dictionary dictionary)
	   (type t token value))
  (dictionary-add-token-info (dictionary-table dictionary) token value))

;;; DICTIONARY-ADD-BUILTIN-SORT : Dictionary Info -> {Dictionary}
;;;
(defun dictionary-add-builtin-sort (dictionary sort)
  (declare (type parse-dictionary dictionary)
	   (type sort* sort))
  (unless (memq sort (dictionary-builtins dictionary))
    (push sort (dictionary-builtins dictionary))))

;;; DICTIONARY-DELETE-INFO-ON-TOKEN : Dictionary Token Value -> {Dictionary}
;;;
(defun dictionary-delete-info-on-token (dictionary token value)
  (declare (type parse-dictionary dictionary)
	   (type t token value))
  (dictionary-delete-token-info (dictionary-table dictionary) token value))

;;;; functions on table component of dictionary

;;; DICTIONARY-GET-TOKEN-INFO : Table Token -> List[Operator+Variable]
(declaim (inline dictionary-get-token-info))

(defun dictionary-get-token-info (table token)
  (declare (type hash-table table)
	   (type t token))
  (gethash token table))

;;; DICTIONARY-REPLACE-TOKEN-INFO : Table Token List[Operator+Variable]
;;;     -> {Table}
(declaim (inline dictionary-replace-token-info))

(defun dictionary-replace-token-info (table token values)
  (declare (type hash-table table)
	   (type t token values))
  (setf (gethash token table) values))

;;; DICTIONARY-DELETE-TOKEN-INFO : Table Token Value -> {Table}
(defun dictionary-delete-token-info (table token value)
  (declare (type hash-table table)
	   (type t token value))
  (let ((values (dictionary-get-token-info table token)))
    (declare (type list values))
    (if (memq value values)
	(let ((new-values (remove value values :test #'eq)))
	  (if (null new-values)
	      (remhash token table)
	      (dictionary-replace-token-info table token new-values))))))

;;; DICTIONARY-ADD-TOKEN-INFO : Table Token Value -> {Table}
(defun dictionary-add-token-info (table token value)
  (declare (type hash-table table)
	   (type t token value))
  (dictionary-replace-token-info table token
				 (adjoin value
					 (dictionary-get-token-info table token)
					 :test #'eq)))


;;; GET-INFO-ON-TOKEN : Dictionary Token -> List[Method+Variable+AST]
;;;
(defun info-for-special-builtins (token)
  (declare (type list token))
  (case (car token)
    ((|String| %string)
     (when (memq *string-sort*
		 (module-all-sorts *current-module*))
       (make-bconst-term *string-sort* (cadr token))))
    #||
    ((|Character| %character)
     (when (memq *character-sort* (module-all-sorts *current-module*))
       (make-bconst-term *character-sort*
			       (character (cadr token)))))
    ||#
    (%slisp (make-simple-lisp-form-term (cadr token)))
    (%glisp (make-general-lisp-form-term (cadr token)))
    (|%Chaos|
     (when (memq *chaos-value-sort*
		 (module-all-sorts *current-module*))
       (make-bconst-term *chaos-value-sort*
			 (cadr token))))
    (otherwise
     (with-output-panic-message ()
       (format t "Internal error: dictionary, unknown type of token ~s" token)
       (chaos-to-top)))))

(defun variable-copy-modifying (var)
  (declare (type term var))
  (@create-variable-term
   (intern (concatenate 'string (the simple-string
				  (string (variable-name var)))
			"'"))
   (variable-sort var)))

(defun simple-copy-term-sharing-variables (term dict)
  (declare (type term term)
	   (type parse-dictionary dict))
  (if (term-is-variable? term)
      (let ((infos (dictionary-get-token-info (dictionary-table dict)
					      (string (variable-name term)))))
	(declare (type list infos))
	(dolist (info infos)
	  (when (and (term-is-variable? info)
		     (sort= (variable-sort term)
			    (variable-sort info)))
	    (return-from simple-copy-term-sharing-variables info)))
	(let ((res (assoc (variable-name term) *parse-variables* :test #'eql)))
	  (declare (type list res))
	  (if res
	      (cdr res)
	    (progn
	      (push (cons (variable-name term) ;; (variable-copy term)
			  term)
		    *parse-variables*)
	      term))))
      (if (term-is-application-form? term)
	  (@create-application-form-term (term-head term)
					 (term-sort term)
					 (mapcar #'(lambda (x)
						     (simple-copy-term-sharing-variables x dict))
						 (term-subterms term)))
	  (simple-copy-term term))))

(defun get-qualified-op-pattern (tok &optional (module (or *current-module*
							   *last-module*)))
  (labels ((destruct-op-name (expr)
	     (let ((pos (position #\_ expr)))
	       (declare (type (or null fixnum) pos))
	       (if pos
		   (cons (subseq expr 0 pos)
			 (list "_"
			       (destruct-op-name
				(subseq expr (1+ pos)))))
		   expr)))
	   (parse-opref (expr)
	     (declare (type string expr))
	     (let ((val (destruct-op-name expr)))
	       (unless (consp val)
		 (setq val (list val)))
	       (let ((name (car val)))
		 (declare (type simple-string name))
		 (let ((pos (position #\. name)))
		   (if (and pos (< 0 pos) (< (1+ pos) (length name)))
		       ;; "foo.qualifier"
		       (values (cons (subseq name 0 pos) (cdr val))
			       (subseq name (1+ pos)))
		       (return-from get-qualified-op-pattern nil))))))
	   (find-qual-operators-2 (name module context)
	     (let ((modval (find-module-in-env-ext (canonicalize-simple-module-name module)
						   context
						   :no-error)))
	       (if (module-p modval)
		   (find-operators-in-module-no-number name modval nil t)
		   (with-output-chaos-error ('invalid-context)
		     (format t "module ~a is not available in the current context." module))))))
    (let ((info nil)
	  (res nil))
      (multiple-value-bind (name qual)
	  (parse-opref tok)
	(setq info (find-qual-operators-2 name qual module))
	(dolist (i info)
	  (if (cdr (opinfo-methods i))
	      (push (cadr (opinfo-methods i)) res)
	    (push (car (opinfo-methods i)) res)))
	(values res name)))))

(defun parser-is-more-general-one (obj lst)
  (and (method-p obj)
       (let ((lowers (method-lower-methods obj)))
	 (dolist (obj2 lst)
	   (when (member obj2 lowers :test #'eq)
	     (return-from parser-is-more-general-one t)))
	 nil)))

(defun get-info-on-token (dictionary token &optional sort-constraint)
  (declare (type parse-dictionary dictionary)
	   (type t token))
  (when *on-parse-debug*
    (format t "~&dictionary info token = ~s" token))
  (let ((res nil)
	(mod-token nil))
    (block collect
      (cond ((consp token)
	     ;; special builtin tokens
	     (setq res (list (info-for-special-builtins token))))
	    ;; normal token
	    (t (setq res (dictionary-get-token-info (dictionary-table dictionary)
						    token))
	       ;; check builtin constant
	       (let (pos)
		 (dolist (bi (dictionary-builtins dictionary))
		   (let ((token-pred (bsort-token-predicate bi)))
		     (when (and token-pred
				(funcall token-pred token))
		       (push bi pos))))
		 (if pos
		     ;; may be builtin constant.
		     (if (cdr pos)
			 (let ((so (module-sort-order
				    *current-module*))) 
			   (dolist (bi pos)
			     (unless (some #'(lambda (x) (sort< x bi so)) pos)
			       (push (dictionary-make-builtin-constant token bi) res))))
		       (push (dictionary-make-builtin-constant token (car pos)) res))))
	       
	       ;; blocked let variable?
	       ;;  *TODO*
	     
	       ;; bound variable?
	       (catch 'term-context-error
		 (let ((val (get-bound-value token)))
		   (when val
		     (if (is-special-let-variable? token)
			 (push val res)
		       (push (simple-copy-term-sharing-variables val dictionary)
			     res)))))
	       ;; try other possiblities.
	       ;; variable ?
	       (let ((res2 (assoc (intern token) *parse-variables*)))
		 (cond (res2
			;; there's a registered variable with name 'token', accumlate
			;; it. now that vars are left in modules want
			;; *parser-variables* to replace.
			(when *on-parse-debug*
			  (format t "~&found var : ~s" (car res2)))
			(setq res (cons (cdr res2) (dictionary-delete-vars res))))
		       (t
			;; check sort qualified variable reference
			;; = on-the-fly (dynamic) variable declaration. 
			(let ((q-pos (position #\: (the simple-string token)
					       :from-end t)))
			  (declare (type (or null fixnum) q-pos))
			  (cond ((and q-pos
				      (not (zerop (the fixnum q-pos)))
				      (not (= (the fixnum q-pos)
					      (the fixnum
						(1- (length
						     (the simple-string token)))))))
				 (let ((sort nil)
				       (var-name nil)
				       (var nil))
				   ;; assumes the token is qualified vriable
				   ;; declaration. 
				   (setq var-name (subseq (the simple-string token)
							  0
							  (the fixnum q-pos)))
				   (setf sort (find-sort-in *current-module*
							    (subseq
							     (the simple-string token)
							     (1+ (the fixnum q-pos)))))
				   (unless sort
				     (when res (return-from collect nil))
				     (with-output-chaos-error ('no-such-sort)
				       (format t "unknown sort ~a for variable form ~a."
					       (subseq token (1+ q-pos))
					       token)))
				   (let ((bi (check-var-name-overloading-with-builtin
					      var-name sort *current-module*)))
				     (when bi
				       (with-output-chaos-warning ()
					 (format t "declaring variable ~s on the fly,"
						 var-name)
					 (print-next)
					 (princ "the name is conflicting with built-in constant of sort ")
					 (print-sort-name bi *current-module*)
					 (princ ".")
					 (terpri))))
				   ;;
				   #||
				   (let ((gv (dictionary-get-token-info
					      (dictionary-table dictionary)
					      var-name)))
				     (when gv
				       (dolist (op-v gv)
					 (when (eq (object-syntactic-type op-v)
						   'variable)
					   (with-output-chaos-error ('already-used-name)
					     (format t "~&on the fly variable name ~A is already used for static variable declaration..." var-name))))))
				   ||#
				   (setq var-name (intern var-name))

				   ;; success parsing it as a variable declaration.
				   ;; checks if there alredy a variable with the same
				   ;; name. 
				   (when *on-parse-debug*
				     (format t "~&on-the-fly var decl: ~A" var-name)
				     (format t "... ~A" *parse-variables*))
				   (let ((old-var (assoc var-name *parse-variables*)))
				     (if old-var
					 (unless (sort= (variable-sort (cdr old-var))
							sort) 
					   (with-output-chaos-error ()
					     (format t "variable ~A has been declared as sort ~A, but now being redefined as sort ~A.~%"
						     (string var-name)
						     (string (sort-id
							      (variable-sort (cdr
									      old-var))))
						     (string (sort-id sort))))
					   ;;(setf (cdr old-var)
					   ;; (make-variable-term sort var-name))
					   )
				       (progn
					 ;; check name, if it start with `, we make
					 ;; pseudo variable
					 (if (eql #\` (char (the simple-string (string var-name)) 0))
					     (setf var (make-pvariable-term sort var-name))
					   (setf var (make-variable-term sort var-name)))
					 (push (cons var-name var) *parse-variables*)))
				     (if old-var
					 (progn
					   (push (cdr old-var) res)
					   #||
					   (when (err-sort-p (variable-sort
							      (cdr old-var)))
					     (pushew (cdr old-var)
						     (module-error-variables
						      *current-module*)))
					   ||#
					   )
				       (let ((svar (assoc var res :test #'equal)))
					 (when *on-parse-debug*
					   (format t "~%!res = ~s" res))
					 (when svar
					   (with-output-chaos-error ()
					     (format t "Static variable ~s already used before in the same context" var-name)))
					 (push var res)
					 #||
					 (when (err-sort-p (variable-sort var))
					   (pushnew var (module-error-variables
							 *current-module*)))
					 ||#
					 )))))

				;; must not be a variable declaration.
				;; try yet other possibilities.
				(t
				 ;; no possibilities of vairable nor builtin
				 ;; constant.
				 (let ((ast (gethash token *builtin-ast-dict*)))
				   (if ast
				       ;; abstract syntax tree.
				       (setf res ast))
				   (unless res
				     (multiple-value-setq (res mod-token)
				       (get-qualified-op-pattern token)))
				   ;;
				   (when (and (null res)
					      (memq *identifier-sort*
						    (module-all-sorts
						     *current-module*)))
				     (let ((ident (intern token)))
				       (unless (member ident '(|.| |,|
							       |(| |)|
							       |{| |}|
							       |[| |]|))
					 (push (make-bconst-term *identifier-sort* ident) res)))))))))))
	       ;; final possibility
	       (unless res
		 (multiple-value-setq (res mod-token)
		   (get-qualified-op-pattern token))))))
    ;; end collect
    (when sort-constraint
      (let ((real-res nil))
	(dolist (r res)
	  (cond ((term? r)
		 (when (parser-in-same-connected-component (term-sort r)
							   sort-constraint
							   *current-sort-order*)
		   (push r real-res)))
		((method-p r)
		 (when (parser-in-same-connected-component (method-coarity r)
							   sort-constraint
							   *current-sort-order*)
		   (push r real-res)))
		(t (push r real-res))))
	(when real-res
	  (setq res real-res))))
    (let ((result nil))
      (loop 
	(unless res (return))
	(let ((p (pop res)))
	  (unless (parser-is-more-general-one p res)
	    (push p result))))
      (setq res (nreverse result)))
    (when *on-parse-debug*
      (format t "~& : sort constraint = ")
      (print-chaos-object sort-constraint)
      (format t "~& : result info = ~s" res)
      (print-chaos-object res))
    (values res (car mod-token))))

(defun dictionary-delete-vars (lst)
  (declare (type list lst))
  (if (dolist (e lst nil)
	(when (consp e) (return t)))
      (let ((res nil))
	(dolist (e lst)
	  (unless (consp e) (push e res)))
	(nreverse res))
      lst))

;;; ** TODO **
;;; DICTIONARY-MAKE-BUILTIN-CONSTANT : Token BuiltinSort : -> Operator
;;;
(defun dictionary-make-builtin-constant (token bsort)
  (declare (type t token)
	   (type sort* bsort))
  (catch 'direct-value
    (let ((value (funcall (bsort-term-creator bsort) token)))
      (make-bconst-term bsort value))))



;;;=============================================================================
;;; 				  PARSE ENGINE
;;;=============================================================================

;;;  the range of precedence (and precedence level) :
;;;  values is [ 0 .. 127 ] :

;;; ************
;;; LITTLE UTILS________________________________________________________________
;;; ************

;;; OBJECT-SYNTACTIC-TYPE : Method+Variable+AST -> Synactic-Type
;;; returns a key indicating a syntactic type of the given object.
;;; Synactic-Type: one of variable antefix latefix juxtaposition ast.
;;; 

(defun object-syntactic-type (e)
  (declare (type t e))
  (cond ((term? e)
	 (if (term-is-variable? e)
	     'variable
	     (if (term-is-builtin-constant? e)
		 'builtin
	       (if (term-is-lisp-form? e)
		   'lisp-form
		 'normal-term))))
	((operator-method-p e)
	 (operator-syntactic-type (method-operator e)))
	(t 'ast)))

(defun operator-parse-category (op)
  (operator-syntactic-type-from-name (operator-token-sequence op)))

;;; ****************
;;; THE PARSE ENGINE____________________________________________________________
;;; ****************

;;; PARSE-TERM : TokenList Module PrecedenceLevel Sort -> List[ TERM ]
;;;       TokenList        -- must not be empty, resposibility of caller.
;;;       Module
;;;       PrecedenceLevel  -- constraint
;;;       Sort             -- constraint
;;;       ->
;;;       LIST[ ( ( ChaosTerm . PrecedenceLevel ) . TokenList ) ] .
;;;         -- possibly empty
;;;  
;;;  var token-list : TokenList
;;;  var module : Module
;;;  var level-constraint : PrecedenceLevel
;;;  var sort-constraint : Sort
;;;
;;;  eq : parser(token-list, module, level-constraint, sort-constraint)
;;;       =
;;;       let ((terletox0-list =
;;;               parser-get-term(token-list, module, level-constraint)))
;;;             -- possibly empty
;;;       (if null(terletox0-list)
;;;         then empty-list
;;;         else parser-continuing(terletox0-list, module,
;;;                             level-constraint, sort-constraint)) .
;;;  
;;;  ** Notes **
;;;  input constraints can be "turned off":
;;;  --   no precedence constraint: give highest precedence (within the range
;;;       of possible values);
;;;  --   no sort constraint: give sort *cosmos*
;;;
;;;  exceptional values:
;;;  --   the standard exceptional value is EMPTY-LIST(= nil); it can be
;;;       returned by parser-get-term, etc.
;;;
;;;  variable naming:
;;;  --  terletox is coined to evoke "TERm-(precedence) LEvel-TOkenlist"
;;;      and is of type ( ( ChaosTerm . PrecedenceLevel ) . TokenList )

;;; ** Note ** parser must not be called on an empty token-list:
;;; responsibility of the caller.

(defun parse-term (token-list module level-constraint sort-constraint)
  (declare (type list token-list)
	   (type module module)
	   (type fixnum level-constraint)
	   (type sort* sort-constraint))
    (let ((terletox0-list (parser-get-term token-list
					   module
					   level-constraint
					   ;; sort-constraint
					   )))
      (declare (type list terletox0-list))
      (let ((res nil))
	(when terletox0-list
	  (setq res (parser-continuing terletox0-list
				       module
				       level-constraint
				       sort-constraint)))
	res)))

;;;  PARSER-CONTINUING :
;;;       LIST[ ( ( ChaosTerm . PrecedenceLevel ) . TokenList ) ]  -- not empty !
;;;       Module
;;;       PrecedenceLevel       -- constraint
;;;       Sort                  -- constraint
;;;       ->
;;;       LIST[ ( ( ChaosTerm . PrecedenceLevel ) . TokenList ) ]
;;;         -- possibly empty
;;;  
;;;  var module : Module 
;;;  var level-constraint : PrecedenceLevel 
;;;  var sort-constraint : Sort
;;;  var E : ( ( ChaosTerm . PrecedenceLevel ) . TokenList )  -- element
;;;  var S : LIST[ ( ( ChaosTerm . PrecedenceLevel ) . TokenList ) ]  -- set
;;;  
;;;  eq : parser-continuing(empty-list, module,
;;;                     level-constraint, sort-constraint)
;;;     = empty-set .
;;;  
;;;  eq : parser-continuing(E adjoined-to S, module,
;;;                      level-constraint, sort-constraint)
;;;    =
;;;    parser-continue-check(E, module, level-constraint, sort-constraint)
;;;     adjoined-to
;;;    parser-continuing(S, module, level-constraint, sort-constraint).

(defun parser-continuing (terletox0-list module level-constraint sort-constraint)
  (declare (type list terletox0-list)
	   (type module module)
	   (type fixnum level-constraint)
	   (type sort* sort-constraint))
  (let ((terletox-list-prime nil))	;initialization--will serve as accumulator
					;  and be returned in the end.
    (dolist (terletox0 terletox0-list terletox-list-prime)
      (setq terletox-list-prime		;accumulate
            (nconc (parser-continue-check terletox0
					  module
					  level-constraint
					  sort-constraint)
                   terletox-list-prime)))))

;;;  PARSER-CONTINUE-CHECK :
;;;       ( ( ChaosTerm . PrecedenceLevel ) . TokenList )
;;;       Module
;;;       PrecedenceLevel  -- constraint
;;;       Sort + { Universal }  -- constraint
;;;       ->
;;;       LIST[ ( ( ChaosTerm . PrecedenceLevel ) . TokenList ) ] .
;;;         -- possibly empty
;;;
;;;  var T0 : ChaosTerm .
;;;  var L0 level-constraint : PrecedenceLevel .
;;;  var token-list : TokenList .
;;;  var module : Module .
;;;  var sort-constraint : Sort + { Universal } .
;;;
;;;  eq parser-continue-check( ( ( T0 . L0 ) . token-list ),
;;;              module, level-constraint, sort-constraint)
;;;     =
;;;     let terletox-list =
;;;       parser-continue( ( ( T0 . L0 ) . token-list ),
;;;                       module, level-constraint, sort-constraint)
;;;         -- possibly empty
;;;     if parser-in-same-connected-component(
;;;                            term-sort(T0),
;;;                            sort-constraint,
;;;                            module-sort-order(module))
;;;       then ( ( T0 . L0 ) . token-list ) adjoined-to terletox-list
;;;       else terletox-list .

(defun parser-continue-check (terletox0 module level-constraint sort-constraint)
  (declare (type list terletox0)
	   (type module module)
	   (type fixnum level-constraint)
	   (type sort* sort-constraint))
  ;;
  (let* ((chaos-term0 (caar terletox0))
	 (sort0 (term-sort chaos-term0))
	 (sort-order (module-sort-order module))
	 ;; add chaos-term0 in the set of solutions if its sort is correct:
	 (terletox-sublist-prime (if (or
				      ;; (term-ill-defined chaos-term0)
				      (parser-in-same-connected-component
				       sort0
				       sort-constraint
				       sort-order))
				     ;; then
				     (list terletox0)
				     ;; else -- completely illegual
				     nil)))
    ;;
    (when *on-parse-debug*
      (format t "~%[continue-check]: const=")
      (print-chaos-object sort-constraint)
      (format t "~%-- target sort=")
      (print-chaos-object sort0)
      (format t "~%-- sublist prime=")
      (print-chaos-object terletox-sublist-prime))
    ;;
    (nconc terletox-sublist-prime
	   (parser-continue terletox0 module level-constraint sort-constraint))))

;;;  PARSER-CONTINUE :
;;;       ( ( ChaosTerm . PrecedenceLevel ) . TokenList )
;;;       Module
;;;       PrecedenceLevel  -- constraint
;;;       Sort + { Universal }  -- constraint
;;;       ->
;;;       LIST[ ( ( ChaosTerm . PrecedenceLevel ) . TokenList ) ] .
;;;         -- possibly empty
;;;  
;;;  var token-list : TokenList .
;;;  var T0 : ChaosTerm .
;;;  var L0 level-constraint : PrecedenceLevel .
;;;  var module : Module .
;;;  var sort-constraint : Sort + { Universal }.
;;;
;;;  eq parser-continue( ( ( T0 . L0 ) . token-list ),
;;;                     module, level-constraint, sort-constraint)
;;;     =
;;;     let current-token = inspect-next-token(token-list)
;;;                            -- inspect but do not swallow
;;;     let choice =
;;;       choose-methods-from-token( ( T0 . L0 ), current-token,
;;;                        module, level-constraint)  -- possibly empty
;;;     if null(choice)
;;;       then empty-list
;;;       else parser-continue-for-operators(token-list, T0, choice,
;;;                              module, level-constraint, sort-constraint) .

(defun parser-continue (terletox0 module level-constraint sort-constraint)
  (declare (type list terletox0)
	   (type module module)
	   (type fixnum level-constraint)
	   (type sort* sort-constraint))
  (let ((token-list (cdr terletox0)) )  ;possibly emtpy 
    (declare (type list token-list))
    (if (null token-list)
	nil
        (let* ((token1 (car token-list))
	       (term-level0 (car terletox0)))
	  (multiple-value-bind (choice mod-token)
	      (choose-operators-from-token term-level0
					   token1
					   module
					   level-constraint)
	    (if (null choice)
		nil			;return a void solution
		(progn
		  (when mod-token
		    (setf (car token-list) mod-token))
		  (parser-continue-for-operators token-list
						 (car term-level0) ;chaos-term0
						 choice
						 module
						 level-constraint
						 sort-constraint))))))))

;  -------------------------------------------------------------------------

;;;  op parser-continue-for-operators :
;;;       TokenList
;;;       ChaosTerm  -- sub-term to build above; an acceptable first argument
;;;       LIST[ LatefixOperator + JuxtapositionOperator ]  -- not empty !
;;;       Module
;;;       PrecedenceLevel  -- constraint
;;;       Sort + { Universal }  -- constraint
;;;       ->
;;;       LIST[ ( ( ChaosTerm . PrecedenceLevel ) . TokenList ) ]
;;;         -- possibly empty
;;;
;;;  var token-list : TokenList .
;;;  var T0 : ChaosTerm .
;;;  var L0 level-constraint : PrecedenceLevel .
;;;  var module : Module .
;;;  var sort-constraint : Sort + { Universal } .
;;;  var E : LatefixOperator + JuxtapositionOperator .  -- element
;;;  var S : LIST[ LatefixOperator + JuxtapositionOperator ] .  -- set
;;;
;;;  eq parser-continue-for-operators(token-list, T0, empty-set, module,
;;;                           level-constraint, sort-constraint)
;;;     = empty-set .
;;;  
;;;  eq parser-continue-for-operators(token-list, T0, E adjoined-to S,
;;;                           module, level-constraint, sort-constraint)
;;;     =
;;;     parser-continue-for-operator(token-list, T0, E, module,
;;;                     level-constraint, sort-constraint)
;;;       adjoined-to
;;;     parser-continue-for-operators(token-list, T0, S, module,
;;;                             level-constraint, sort-constraint) .
;;;
(defun parser-continue-for-operators (token-list
				      chaos-term0
				      late-juxt-operator-list
				      module level-constraint sort-constraint)
  (declare (type list token-list late-juxt-operator-list)
	   (type t chaos-term0)
	   (type module module)
	   (type fixnum level-constraint)
	   (type sort* sort-constraint))
  (let ((terletox-list-prime nil))	;initialization--to be returned in the end
    (dolist (late-juxt-operator late-juxt-operator-list terletox-list-prime)
      (when *on-parse-debug*
	(format t "~&continue : try method ")
	(print-chaos-object late-juxt-operator))
      (setq terletox-list-prime
            (nconc (parser-continue-for-operator token-list
						 chaos-term0
						 late-juxt-operator
						 module
						 level-constraint
						 sort-constraint)
                   terletox-list-prime)))))

;;;  op parser-continue-for-operator :
;;;       TokenList
;;;       ChaosTerm  -- sub-term to build above; an acceptable first argument
;;;       LatefixOperator + JuxtapositionOperator
;;;       Module
;;;       PrecedenceLevel  -- constraint
;;;       Sort + { Universal }  -- constraint
;;;       ->
;;;       LIST[ ( ( ChaosTerm . PrecedenceLevel ) . TokenList ) ] .
;;;         -- possibly empty
;;;  
;;;  var token-list : TokenList .
;;;  var T0 : ChaosTerm .
;;;  var level-constraint : PrecedenceLevel .
;;;  var operator : LatefixOperator + JuxtapositionOperator .
;;;  var module : Module .
;;;  var sort-constraint : Sort + { Universal } .
;;;  
;;;  eq parser-continue-for-operator(token-list, T0, operator, module,
;;;                     level-constraint, sort-constraint)
;;;     =
;;;     let first-result =
;;;           parser-finish-term-for-operator(token-list, T0, operator, module)
;;;                 -- possibly an empty list
;;;     if null(first-result)
;;;       then nil
;;;       else
;;;         parser-continuing(first-result, module,
;;;                        level-constraint, sort-constraint) .
;;;  
;;;  -- Note: parser-continue-for-operator is not called unless operator
;;;  --    is a latefix operator or a juxtaposition operator,
;;;  --    and is so far an acceptable operator.

(defun parser-continue-for-operator (token-list
				     chaos-term0
				     late-juxt-operator
				     module level-constraint sort-constraint)
  (declare (type list token-list)
	   (type method late-juxt-operator)
	   (type t chaos-term0)
	   (type module module)
	   (type fixnum level-constraint)
	   (type sort* sort-constraint))
  (let ((first-result-list (parser-finish-term-for-operator token-list
							    chaos-term0
							    late-juxt-operator
							    module)))
    (if (null first-result-list)
	nil				;return an empty solution
      (parser-continuing first-result-list
			 module
			 level-constraint
			 sort-constraint))))

;;;  op parser-finish-term-for-operator :
;;;       TokenList
;;;       ChaosTerm  -- an acceptable first argument
;;;       LatefixOperator + JuxtapositionOperator
;;;         -- a so far acceptable latefix or juxtaposition operator to try
;;;       Module
;;;       -> LIST[ ( ( ChaosTerm . PrecedenceLevel ) . TokenList ) ] .
;;;            -- possibly empty
;;;
;;;-- Notes:
;;;-- 1. This procedure is not called, unless:
;;;--	a. the next token to swallow is the first token part of the latefix
;;;--           operator given as input argument; or refers to a variable, a
;;;--           constant, a function, a prefix part of an operator or is "(";
;;;--	b. the latefix or juxtaposition operator given as input is
;;;--           acceptable so far, i.e. with regard to sort and precedence of
;;;--           the subterm obtained so far.
;;;
;;;-- 2.
;;;subsorts LatefixOperator < Operator .
;;;-- An operator is of sort LatefixOperator if its pattern starts with:
;;;-- "_" followed by a token and possibly other things, e.g. "_ + _", "_ !",
;;;-- "_ [ _ ]".
;;;
;;;-- 3.
;;;subsorts JuxtapositionOperator < Operator .
;;;-- An operator is of sort JuxtapositionOperator if its pattern starts with:
;;;-- "_ _", e.g. "_ _", "_ _ _ ", "_ _ _ foo _".
;;;
(defun parser-finish-term-for-operator (token-list chaos-term0
						   late-juxt-operator module)
  (declare (type list token-list)
	   (type t chaos-term0 late-juxt-operator)
	   (type module module))
  ;;
  (let* ((form (method-form late-juxt-operator))
	 (rest-form (cdr form))		;we already got the first argument
	 (arg-acc-list (list (cons (list chaos-term0) token-list))) ;initialization
	 (arg-acc-list-prime		;possibly nil
	  (parser-collect-arguments arg-acc-list
				    module
				    rest-form)))
    (if (null arg-acc-list-prime)
	;; illegal
	;; (parser-make-terms late-juxt-operator arg-acc-list module)
	nil
      (parser-make-terms late-juxt-operator arg-acc-list-prime module))))

;;;  op parser-get-term : 
;;;       TokenList  -- not empty !
;;;       Module
;;;       PrecedenceLevel  -- constraint
;;;       ->
;;;       LIST[ ( ( ChaosTerm . PrecedenceLevel ) . TokenList ) ] .
;;;         -- possibly empty

(defun parser-get-term (token-list module level-constraint
				   &optional sort-constraint)
  (declare (type list token-list)
	   (type module module)
	   (type fixnum level-constraint))
  (let ((token1 (car token-list))	;token-list non null
	(token-list-prime (cdr token-list)))
    (when *on-parse-debug*
      (format t "~%[parser-get-term]: token-list=~s" token-list)
      (format t " sort-constraint: ~a" (if sort-constraint
					   (string (sort-name sort-constraint))
					 "None")))
    (when (and (symbolp token1)
	       (memq token1 '(%slisp %glisp |%Chaos|)))
      (return-from parser-get-term nil))
    ;;what first token have we got ?
    (cond ((equal token1 "(")
	   ;;* Reserved tokens
	   ;;* Parenthesized expression
	   (if (null token-list-prime)
	       nil			;return an empty set of solutions
	     (parser-get-rest-of-parenthesized-expr token-list-prime
						    module)))
	  (;; (member token1 '( ")" "," ) :test #'equal)
	   (equal token1 ")")
	   ;;* Unacceptable reserved tokens
	   nil )			;return empty set of solutions
	  ;;* Regular tokens
	  ;;  They have to have been declared operators or variables:
	  (t (get-term-for-regular-token token1
					 token-list-prime
					 module
					 level-constraint
					 sort-constraint)))))

;;;  op parser-get-rest-of-parenthesized-expr :
;;;       TokenList  -- not empty !
;;;       Module
;;;       ->
;;;       LIST[ ( ( ChaosTerm . PrecedenceLevel ) . TokenList ) ] .
;;;         -- possibly empty
;;;
(defun parser-get-rest-of-parenthesized-expr (token-list module)
  (declare (type list token-list)
	   (type module module))
  (let ((terletox-list (parse-term token-list
				   module
				   parser-max-precedence
				   ;; sort-constraint
				   *cosmos*))
	(terletox-list-prime nil)	; accumulator--to be returned in the end
	terletox)
    (declare (type list terletox-list))
    ;; this is "over-general"
    ;; group terms together with same remaining token list
    ;; check for possible term qualification, if present treat
    ;; group of terms as a unit
    (loop (when (null terletox-list) (return terletox-list-prime))
	  (setq terletox (car terletox-list))
	  (setq terletox-list (cdr terletox-list))
	  (let ((token-list (cdr terletox))
		(chaos-terms (list (caar terletox)))
		(rest-terletox-list nil))
	    (dolist (tlt terletox-list)
	      (if (eq (cdr tlt) token-list)
		  (push (caar tlt) chaos-terms) ;use rplacd for space ??
		  (push tlt rest-terletox-list)))
	    (setq terletox-list rest-terletox-list)
	    ;; for each solution, try to swallow ")";
	    (if (equal (car token-list) ")")
		;; token-list is not empty and begins with ")":
		;; then swallow ")", set precedence level to 0, and accumulate:
		(if (and (cdr token-list)
			 (let ((fst (char (the simple-string
					    (cadr token-list))
					  0))
			       (info (get-info-on-token
				      (module-parse-dictionary *current-module*)
				      (cadr token-list))))
			   (and (eql #\: fst)
				(not (equal (cadr token-list) ":is"))
				(dolist (in info t)
				  (when (member (object-syntactic-type in)
						'(antefix juxtaposition latefix))
				    (return nil))))))
		    ;; !! might modify this last condition a bit
		    (multiple-value-bind (terms toks)
			(parser-scan-qualification chaos-terms
						   (cdr token-list))
		      (dolist (tm terms)
			(setq terletox-list-prime
			      (cons (cons (cons tm parser-min-precedence)
					  toks)
				    terletox-list-prime))))
		  ;; else: there isn't a qualification; create continuations
		  (dolist (tm chaos-terms)
		    (setq terletox-list-prime
		      (cons (cons (cons tm parser-min-precedence)
				  (cdr token-list))
			    terletox-list-prime))))
	      nil)))))

;;;  op parser-scan-qualification : TermList TokenList -> TermList TokenList
;;;  Token list starts with the qualification; for ((x + y) . A) is (. A)
;;;

(defun parser-scan-qualification (chaos-terms token-list)
  (declare (type list chaos-terms token-list))
  (let ((tokens (if (equal (car token-list) ":")
		    (cdr token-list)
		  (cons (subseq (the simple-string (car token-list)) 1)
			(cdr token-list))))
	(res nil)
	qualifier
	rest)
    (if (equal "(" (car tokens))
	(let ((paren-pair (parser-scan-parenthesized-unit tokens)))
	  (declare (type list paren-pair))
	  (if (null paren-pair) (setq res 'unbalanced)
	      (setq qualifier (if (atom (car paren-pair))
				  (list (car paren-pair))
				  (car paren-pair))
		    rest (cdr paren-pair))))
	(setq qualifier (list (car tokens))  rest (cdr tokens)))
    (when *on-parse-debug*
      (format t "~&[scan-qualification] tokens=~a" tokens))
    (if (eq 'unbalanced res)
	(values chaos-terms token-list)
	(let ((sorts (find-all-sorts-in *current-module* qualifier))
	      (exact nil)
	      (res nil)
	      tm)
	  (when *on-parse-debug*
	    (format t "~&[scan-qualification] qualifier=~a" qualifier))
	  (unless sorts ;; was qualifier
	    (with-output-chaos-error ('no-such-sort)
	      (format t "no such sort ~a" qualifier)))
	  ;; should give error message. and abort.
	  (loop (when (null chaos-terms) (return))
	      (setq tm (car chaos-terms))
	    (setq chaos-terms (cdr chaos-terms))
	    (let ((t-sort (term-sort tm)))
	      (when (some #'(lambda (x) (sort<= t-sort x)) sorts)
		(push tm res))
	      (when (memq t-sort sorts)
		;; (setq exact tm)
		(push tm exact))
		;; (return nil)
	      ))
	  ;;
	  (when *on-parse-debug*
	    (format t "~& ...exect found: ")
	    (print-chaos-object exact))
	  ;;
	  (if exact
	      ;; (values (list tm) rest)
	      (values exact rest)
	    (values res rest))))))

(defun parser-scan-parenthesized-unit (tokens)
  (declare (type list tokens))
  (if (equal "(" (car tokens))
      (let ((count 1) (lst (cdr tokens)) (res nil))
	(declare (type fixnum count))
	(loop (when (null lst) (return 'unbalanced))
	      (let ((tok (car lst)))
		(setq lst (cdr lst))
		(when (and (= 1 count) (equal ")" tok))
		  (return (cons (if (and res (null (cdr res)))
				    (car res)
				    (nreverse res))
				lst)))
		(setq res (cons tok res))
		(if (equal "(" tok) (incf count)
		    (if (equal ")" tok) (decf count))))))
      tokens))

;;;  op get-term-for-regular-token :
;;;       Token
;;;       TokenList  -- possibly empty !
;;;       Module
;;;       PrecedenceLevel  -- constraint
;;;       ->
;;;       LIST[ ( ( ChaosTerm . PrecedenceLevel ) . TokenList ) ] .
;;;         -- possibly empty

(defun get-term-for-regular-token (token token-list module level-constraint
					 &optional sort-constraint)
  (declare (type t token)
	   (type list token-list)
	   (type module module)
	   (type fixnum level-constraint))
  (flet (
	 #||
	 (make-syntax-error ()		; never used now
	   (list
	    (list
	     (list (make-applform
		    *op-err-sort*
		    *op-err-method*
		    (list (make-bconst-term *string-sort* token)
			  (make-bconst-term *universal-sort*
					    token-list)))))))
	 ||#
	 )
    ;;
    (let ((terletox-list-prime nil))	; accumulator
      (multiple-value-bind (op-var-list mod-token)
	  (get-info-on-token (module-parse-dictionary module)
			     token
			     )
	(declare (ignore mod-token))
	;; list of Operators and Variables--token is the first token
	;;  to appear in the pattern !
	;; If choice between operators of
	;;  comparable sorts ?  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	;; for each operator or variable, go ahead and collect solutions
	(if (and op-var-list
		 (not (equal op-var-list '(()))))
	    (dolist  (op-var op-var-list
		      #||
		      (if (null terletox-list-prime)
			  (make-syntax-error)
			  terletox-list-prime)
		      ||#
		      terletox-list-prime)
	      ;; (op-var op-var-list terletox-list-prime)
	      (let ((res (get-term-for-op-var op-var
					      token-list
					      module
					      level-constraint
					      sort-constraint)))
		(when res
		  (when *on-parse-debug*
		    (format t "~%[get-term-for-regular-token]: ")
		    (format t "~% res = ")
		    (print-chaos-object res))
		  (if (or ;; (not *fast-parse*)
			  (memq (object-syntactic-type op-var)
				'(variable builtin lisp-form normal-term))
			  (and (method-p op-var)
			       ;; (null (method-arity op-var))
			       ))
		      (setq terletox-list-prime ; accumulate
			    (nconc res terletox-list-prime))
		    (return-from get-term-for-regular-token
		      (nconc res terletox-list-prime)))))))))))

;;;  op get-term-for-op-var :
;;;       Operator(Mehotd) + Variable
;;;       TokenList  -- possibly empty
;;;       Module
;;;       PrecedenceLevel  -- constraint
;;;       ->
;;;       LIST[ ( ( ChaosTerm . PrecedenceLevel ) . TokenList ) ] .
;;;         -- possibly empty
(defun get-term-for-op-var (op-var token-list module level-constraint
				   &optional sort-constraint)
  (declare (type t op-var)
	   (type list token-list)
	   (type module module)
	   (type fixnum level-constraint))
  (when *on-parse-debug*
    (format t "~%[get-term-for-op-var]: op-var = ~s, syntactic-type = ~s"
	    op-var (object-syntactic-type op-var))
    (format t "~% sort constraint = ")
    (print-chaos-object sort-constraint))
  (case (object-syntactic-type op-var)
    ;; 1. TERMS
    ;;    Note: a variable is referenced by *ONE* token--always !
    ((variable builtin lisp-form normal-term)
     ;; return a list of only one solution (precedence level is ):
     (when (eq (object-syntactic-type op-var) 'variable)
       (push (cons (variable-name op-var) op-var) *parse-variables*))
     (if (or (null sort-constraint)
	     (sort<= (term-sort op-var) sort-constraint *current-sort-order*))
	 (list (cons (cons op-var parser-min-precedence) token-list))
       nil))

    ;; 2. Antefix
    (antefix
     (when sort-constraint
       (unless (sort<= (method-coarity op-var) sort-constraint *current-sort-order*)
	 (return-from get-term-for-op-var nil)))
     ;; is precedence of antefix operator acceptable ?
     (unless (<= (the fixnum (get-method-precedence op-var))
		 level-constraint)
       (return-from get-term-for-op-var nil))
     (let ((res (get-term-from-antefix-operator op-var token-list module)))
       res))

    ;; 3. Ast
    (ast
     (get-term-from-ast-operator op-var token-list module))
    
    ;; 4. token does not belong to sub-formula.
    ;; return a void solution
    (otherwise nil)))

;;;  op get-term-from-antefix-operator :
;;;       Operator  -- must be antefix !
;;;       TokenList  -- possibly empty
;;;       Module
;;;       -> LIST[ ( ( ChaosTerm . PrecedenceLevel ) . TokenList ) ] .
;;;            -- possibly empty

(defun get-term-from-antefix-operator (method token-list module)
  (declare (type method method)
	   (type list token-list)
	   (type module module))
  (let* ((form (method-form method))
	 (rest-form (cdr form))		;we already swallowed the first token
	 ;;rest-form possibly empty
	 (arg-acc-list (list (cons nil token-list))) ;initialization
	 (arg-acc-list-prime (parser-collect-arguments arg-acc-list
						       module
						       rest-form)))
    (if (null arg-acc-list-prime)
	;; return a void answer
	;; (parser-make-terms method arg-acc-list module)
	nil
      (parser-make-terms method arg-acc-list-prime module))))

;;; AST
;;;
(defun get-term-from-ast-operator (key token-list module)
  (declare (type list key token-list)
	   (type module module))
  (let* ((form (cdr key))
	 (rest-form (cdr form))
	 (arg-acc-list (list (cons nil token-list)))
	 (arg-acc-list-prime (parser-collect-arguments arg-acc-list
						       module
						       rest-form)))
    (when *on-parse-debug*
      (format t "~& rest-form = ")
      (print-chaos-object rest-form))

    (if (null arg-acc-list-prime)
	nil
	(parser-make-terms key arg-acc-list-prime module))))

;;;  op choose-operators-from-token :
;;;       ( ChaosTerm . PrecedenceLevel )
;;;       Token  -- the coming token
;;;       Module
;;;       PrecedenceLevel  -- constraint
;;;       ->
;;;       LIST[ LatefixOperator + JuxtapositionOperator ] .
;;;         -- possibly empty; any operator in the list is either latefix
;;;         --   (i.e. of pattern { - <Token> <etc> } ) or juxtapositional
;;;         --   (i.e. of pattern { - - <etc> } ).

(defun choose-operators-from-token (term-level0 token module level-constraint
						&optional sort-constraint)
  (declare (type t term-level0 token)
	   (type module module)
	   (type fixnum level-constraint))
  (when *on-parse-debug*
    (format t "~%[choose-operators-from-token]: token = ~s" token)
    (format t "~% sort constraint = ")
    (print-chaos-object sort-constraint))
  (cond ((equal token "(") 
	 (choose-juxtaposition-operators term-level0 module level-constraint))
	(;; (member token '( ")" "," ) :test #'equal)
	 (equal token ")")
	 nil )
					; return a void answer
	;; Regular tokens
	(t
	 (multiple-value-bind (op-var-list mod-token)
	     (get-info-on-token (module-parse-dictionary module)
				token
				sort-constraint)
	   (if (null op-var-list)
	       nil			;
	     (values (parser-choosing-operators term-level0
						op-var-list
						module
						level-constraint)
		     mod-token))))))

;;;  op parser-choosing-operators :
;;;       ( ChaosTerm . PrecedenceLevel )
;;;       LIST[ Operator + Variable ]  -- non empty !
;;;       Module
;;;       PrecedenceLevel  -- constraint
;;;       ->
;;;       LIST[ LatefixOperator + JuxtapositionOperator ] .

(defun parser-choosing-operators (term-level0 op-var-list module level-constraint)
  (declare (type t term-level0)
	   (type list op-var-list)
	   (type module module)
	   (type fixnum level-constraint))
  (let ((late-juxt-op-list-prime nil))
    (dolist (op-var op-var-list
	     (progn (when *on-parse-debug*
		      (format t "~%[parser-choosing-operators]:~%-- selected ops : ")
		      (print-chaos-object late-juxt-op-list-prime))
		    late-juxt-op-list-prime))
      (setq late-juxt-op-list-prime  ;accumulate
	    (union (choose-operators term-level0
				     op-var
				     module
				     level-constraint)
		   late-juxt-op-list-prime)))))

;;;  op choose-operators :
;;;       ( ChaosTerm . PrecedenceLevel )
;;;       Operator + Variable
;;;       Module
;;;       PrecedenceLevel  -- constraint
;;;       ->
;;;       LIST[ LatefixOperator + JuxtapositionOperator ] .
;;;
(defun choose-operators (term-level0 op-var module level-constraint)
  (declare (type t term-level0 op-var)
	   (type module module)
	   (type fixnum level-constraint))
  (case (object-syntactic-type op-var)
    ;; 1.
    (variable (choose-juxtaposition-operators term-level0
					      module
					      level-constraint))
    ;; 2.
    (antefix				; is op-var acceptable with regard to
					; level-constraint ?
     (if (<= (the fixnum (get-method-precedence op-var))
	     level-constraint) 
	 (choose-juxtaposition-operators term-level0
					 module
					 level-constraint)
	 nil				;return a void answer
	 ))
    ;; 3.
    (ast
     (choose-juxtaposition-operators term-level0 module level-constraint))
     
    ;; 4.
    (latefix (choose-latefix-operators  term-level0
					op-var
					module
					level-constraint))
    ;; 4. builtin
    (builtin (choose-juxtaposition-operators term-level0 module level-constraint))
    ;; 5. others
    (otherwise nil)))

;;;  op choose-juxtaposition-operators :
;;;       ( ChaosTerm . PrecedenceLevel )  -- a possible first argument
;;;       Module
;;;       PrecedenceLevel  -- constraint
;;;       ->
;;;       LIST[ JuxtapositionOperator ] .
;;;         -- possibly empty
;;;  Abstract: return juxtaposition operators
;;;    - of acceptable precedence with regard to level-constraint
;;;    - able to accept term-level0 as a first argument
;;;      (check sort and precedence)

(defun choose-juxtaposition-operators (term-level0 module level-constraint)
  (declare (type t term-level0)
	   (type module module)
	   (type fixnum level-constraint))
  (let ((juxt-op-list (module-juxtaposition module)) )
    (if (null juxt-op-list)
	nil				; return a void answer
      (let ((res nil))
	(dolist (juxt-op juxt-op-list res)
	  (when (and (<= (the fixnum
			   (get-method-precedence juxt-op))
			 level-constraint)
		     (parser-check-operator term-level0 juxt-op module))
	    (setq res (cons juxt-op res))))))))

;;;  op choose-latefix-operators :
;;;       ( ChaosTerm . PrecedenceLevel )
;;;       LatefixOperator
;;;       Module
;;;       PrecedenceLevel  -- constraint
;;;       ->
;;;       LIST[ LatefixOperator ] 
;;;         -- empty or singleton !
;;;  Abstract: return a singleton list containing latefix-operator if it is:
;;;    - of acceptable precedence with regard to level-constraint
;;;    - able to accept term-level0 as a first argument
;;;      (check sort and precedence)

(defun choose-latefix-operators (term-level0 latefix-operator module level-constraint)
  (declare (type t term-level0)
	   (type method latefix-operator)
	   (type module module)
	   (type fixnum level-constraint))
  (if (and (<= (the fixnum (get-method-precedence latefix-operator))
	       level-constraint)
	   (parser-check-operator term-level0
				  latefix-operator
				  module))
      (list latefix-operator)
    ;; return a void answer
    nil))

;;;  op parser-check-operator :
;;;       ( ChaosTerm . PrecedenceLevel )
;;;       JuxtapositionOperator + LatefixOperator
;;;       Module
;;;       ->
;;;       Bool .

;;;  Abstract: check that term-level0 is acceptable to
;;;    late-juxt-op as a first argument: check sorts and precedences.

(defun parser-check-operator (term-level0 late-juxt-op module)
  (declare (type list term-level0)
	   (type method late-juxt-op)
	   (type module module))
  (let* ((sort0 (term-sort (car term-level0)))
	 (level0 (cdr term-level0))
	 (form (method-form late-juxt-op))
	 (first-arg-constraints (car form))
	 (first-arg-level-constraint (or (cadr first-arg-constraints) 0))
	 (first-arg-sort-constraint (car (method-arity late-juxt-op)))
	 (sort-order (module-sort-order module)))
    (declare (type fixnum level0 first-arg-level-constraint))
    (and (<= level0 first-arg-level-constraint)
	 (parser-in-same-connected-component sort0
					     first-arg-sort-constraint
					     sort-order))))

;;;  op parser-collect-arguments :
;;;       LIST[ ( ChaosTermList . TokenList ) ]  -- not empty !
;;;       Module
;;;       Form  -- possibly empty
;;;       ->
;;;       LIST[ ( ChaosTermList . TokenList ) ]
;;;
;;;  Form = LIST[ ( Flag . Value ) ]
;;;  Flag = { 'token, 'argument, 'argument*, 'argument+}
;;;  Value = if flag is 'token then Token  -- the token to swallow
;;;          if         'argument then ( PrecedenceLevel . Sort )
;;;                                      -- constraints on sub-formula
;;;  Examples
;;;  1. A Form value for Natural addition is:
;;;   '( (argument . ( <precedence level constraint> . <sort Natural> ) )
;;;      (token . "+")
;;;      (argument . ( <precedence level constraint> . <sort Natural> ) )
;;;    )
;;;  2. A Form value for some binary function is:
;;;   '( (token . "foo")
;;;      (token . "(")
;;;      (argument . ( 127 . <a Sort value> ) )
;;;      (token . ",")
;;;      (argument . ( 127 . <a Sort value> ) )
;;;      (token . ")")
;;;    )
;;;
(defun parser-collect-arguments (arg-acc-list module rest-form)
  (declare (type list arg-acc-list)
	   (type module module)
	   (type list rest-form))
  (let ((arg-acc-list-prime arg-acc-list))
    (dolist (form-item rest-form)
      (case (car form-item)
	;; 1.
	(token (setq arg-acc-list-prime
		     (parser-scan-token arg-acc-list-prime (cdr form-item))))
	;; 2.
	(argument (setq arg-acc-list-prime
			(parser-collect-one-argument arg-acc-list-prime
						     module
						     (cadr form-item)
						     (cddr form-item))))
	;; 3. collect varargs. --- to be done.
	((argument* argument+)
	 (let ((limit 256))		; for avoiding infinite loop
	   (declare (type fixnum limit))
	   (loop 
	    (decf limit)
	    (when (<= limit 0)
	      (with-output-chaos-warning ()
		(format t "over 256 arguments for argument*")
		(return-from parser-collect-arguments nil)))
	    (when (eq 'argument+ (car form-item))
	      (setf arg-acc-list-prime
		    (parser-collect-one-argument arg-acc-list-prime
						 module
						 (cadr form-item)
						 (cddr form-item)))
	      (unless arg-acc-list-prime (return)))
	    (let ((tok (parser-scan-token arg-acc-list-prime ")")))
	      (if tok
		  (progn (setf arg-acc-list-prime tok)
			 (return))
		  (setq arg-acc-list-prime
			(parser-collect-one-argument arg-acc-list-prime
						     module
						     (cadr form-item)
						     (cddr form-item)))))))))
      (if (null arg-acc-list-prime)
	  (return nil)
	  ;; to avoid unnecessary additional loops, and to avoid calling
	  ;;  either parser-scan-token or
	  ;;  parser-collect-one-argument with void arguments.
	))
    ;; a bit optimization
    #||
    (let ((res nil))
      (when *on-parse-debug*
	(dotimes (x (length arg-acc-list-prime))
	  (format t "~%*** acc-arg #~D : " x)
	  (print-chaos-object (car (nth x arg-acc-list-prime)))
	  (format t "|| tokens ~a" (cdr (nth x arg-acc-list-prime)))))
      (setq res (remove-if #'(lambda (x)
			       (not (term-is-really-well-defined (car x))))
			   arg-acc-list-prime))
      (when (< (length res) (length arg-acc-list-prime))
	(print-in-progress "!"))
      (or res arg-acc-list-prime))
    ||#
    arg-acc-list-prime))

;;;  op parser-collect-one-argument :
;;;       LIST[ ( ChaosTermList . TokenList ) ]  -- not empty !
;;;       Module
;;;       PrecedenceLevel  -- constraint
;;;       Sort + { Universal }  -- constraint
;;;       ->
;;;       LIST[ ( ChaosTermList . TokenList ) ]

(defun parser-collect-one-argument (arg-acc-list module
						 level-constraint sort-constraint)
  (declare (type list arg-acc-list)
	   (type module module)
	   (type fixnum level-constraint)
	   (type sort* sort-constraint))
  (let ((arg-acc-list-prime nil))
    (dolist (arg-acc arg-acc-list (delete-duplicates arg-acc-list-prime :test #'equal))
      (let ((token-list (cdr arg-acc)) )
        (if (null token-list)
	    nil				;this iteration is finished
	  (let* ((arg-list (car arg-acc))
		 (terletox-list (parse-term token-list
					    module
					    level-constraint
					    sort-constraint)))
	    ;; notice that parser is not called with
	    ;;  token-list empty
	    (dolist (terletox terletox-list)
	      ;; if terletox-list empty, no effect
	      (let* ((arg-prime (caar terletox))
		     (token-list-prime (cdr terletox))
		     (arg-list-prime (cons arg-prime arg-list))
		     ;; notice that we accumulate arguments in reverse order
		     (arg-acc-prime (cons arg-list-prime token-list-prime)))
		(setq arg-acc-list-prime
		  (cons arg-acc-prime arg-acc-list-prime))))))))))

;;;  op parser-scan-token :
;;;       LIST[ ( ChaosTermList . TokenList ) ]  -- not empty !
;;;       Token  -- ie Lisp character string
;;;       ->
;;;       LIST[ ( ChaosTermList . TokenList ) ]
;;;
(defun parser-scan-token (arg-acc-list token)
  (declare (type list arg-acc-list)
	   (type t token))
  (let ((arg-acc-list-prime nil))
    (dolist (arg-acc arg-acc-list arg-acc-list-prime)
      (let ((token-list (cdr arg-acc)))
        (if (equal token (car token-list))
	    ;; token-list is not empty and begins with expected token
            (let* ((token-list-prime (cdr token-list))
		   (arg-list (car arg-acc))
		   (arg-acc-prime (cons arg-list token-list-prime)))
              (setq arg-acc-list-prime
                    (cons arg-acc-prime arg-acc-list-prime)))
	    nil)))))

;;;  op parser-in-same-connected-component :
;;;     Sort Sort SortOrder -> Bool 
;;;
(defun parser-in-same-connected-component (sort1 sort2 sort-order)
  #-GCL (declare (inline sort<))
  (or (sort= sort1 sort2)
      (sort= sort1 *cosmos*)
      (sort= sort2 *cosmos*)
      (sort= sort1 *bottom-sort*)
      (sort= sort2 *bottom-sort*)
      (if (err-sort-p sort2)
	  (sort= sort2 (the-err-sort sort1 sort-order))
	  (and (eq (sort-hidden sort1) (sort-hidden sort2))
	       (or (if (sort-is-hidden sort1)
		       (sort= sort2 *huniversal-sort*)
		       (sort= sort2 *universal-sort*))
		   (sort< sort1 sort2 sort-order)
		   (sort< sort2 sort1 sort-order)
		   (is-in-same-connected-component sort1 sort2 sort-order))))))

;;;  op parser-make-terms :
;;;       Operator
;;;       LIST[ ( LIST[ ChaosTerm ] . TokenList ) ]  -- not empty
;;;       Module
;;;       -> LIST[ ( ( ChaosTerm . PrecedenceLevel ) . TokenList ) ] .
;;;            -- possibly empty
;;;
;;;  Remark. This function is called by:
;;;    parser-finish-term-for-operator and get-term-from-antefix-operator

(defun parser-make-terms (method arg-acc-list module)
  (declare (type t method)
	   (type list arg-acc-list)
	   (type module module))
  (when *on-parse-debug*
    (format t "~&make term~% : method = ")
    (print-chaos-object method)
    (format t "~& : arg-acc-list = ")
    (map nil #'print-chaos-object arg-acc-list)
    (force-output))
  (let ((terletox-list nil))
    (dolist (arg-acc arg-acc-list)
      ;; arg-acc ::= (LIST[ChaosTerm] . TokenList)
      (block iteration
        (let* ((arg-list (car arg-acc))
	       (direct-arg-list (reverse arg-list))
	       ;; arguments were accumulated in reverse order !
	       (arg-sort-list (mapcar #'(lambda (x) (term-sort x)) direct-arg-list))
	       ;; arg-sort-list: list of argument sorts
	       (method-prime method)	;initialization
	       (chaos-term nil)		;reservation
	       (precedence-level (get-method-precedence method))
	       (token-list (cdr arg-acc))
	       (terletox nil) )		;reservation
	  (declare (type fixnum precedence-level))
	  (when *on-parse-debug*
	    (format t "~& : method prime = ")
	    (print-chaos-object method-prime)
	    (force-output))
          (if (are-argumentsorts-correct method arg-sort-list module)
	      (progn
		;; ordinal term
		(when (or (method-is-universal* method)
			  (method-is-error-method method))
		  (setq method-prime
			(lowest-method! method arg-sort-list))
		  (when *on-parse-debug*
		    (format t "~& : arg sort list = ~a" arg-sort-list)
		    (format t "~& : lowest method = ")
		    (print-chaos-object method-prime)
		    (force-output))
		  (unless method-prime
		    ;; then no result this iteration; do not accumulate:
		    (return-from iteration nil))
		  )
		;;
		(setq chaos-term
		      (if (are-well-defined-terms direct-arg-list)
			  (parser-make-applform (method-coarity method-prime)
						method-prime
						direct-arg-list)
			  (make-inheritedly-ill-term
			   method-prime direct-arg-list)))
		;; check for _:is_, sortmembership predicate
		#||
		(when (eq *sort-membership* method-prime)
		  (unless (test-sort-memb-predicate chaos-term)
		    (setq chaos-term
			  (make-directly-ill-term method-prime
						  direct-arg-list))))
		||#
		)
	      ;;
	      ;; incorrect argument(s).
	      (progn
		(when *on-parse-debug*
		  (format t "~&incorrenct args, meth= ")
		  (print-chaos-object method)
		  (print-chaos-object arg-sort-list))
		(setq chaos-term
		      (make-directly-ill-term method direct-arg-list))))

	  ;; accummlate possible parses.
	  ;;
	  (when chaos-term
	    (setq terletox (cons (cons chaos-term precedence-level) token-list)
		  terletox-list (cons terletox terletox-list)))
	  ;;
	  (when *on-parse-debug*
	    (format t "~& : chaos-term=")
	    (term-print chaos-term)
	    (format t "~& : terletox=")
	    (print-terletox terletox))
	  ))				; block iteration
      )					; dolist
    (when *on-parse-debug*
      (format t "~& : result = ")
      (print-terletox-list terletox-list))
    terletox-list))

(defun test-sort-memb-predicate (term &optional (module (or *current-module*
							     *last-module*)))
  (unless module
    (with-output-chaos-error ('no-context)
      (princ "checking _:_, no context module is given!")))
  (with-in-module (module)
    (let ((arg1 (term-arg-1 term))
	  (id-const (term-arg-2 term)))
      ;; (format t "~&arg1 = ")(print arg1)
      ;; (format t "~&id-const = ") (print id-const)
      (let ((sorts (gather-sorts-with-id id-const module))
	    (term-sort (term-sort arg1)))
	(unless sorts
	  (with-output-chaos-error ('no-sort)
	    (format t "_:_, no such sort ~a in the current context."
		    (get-sort-id-value id-const))))
	(if (some #'(lambda (x)
		      (parser-in-same-connected-component x
							  term-sort
							  *current-sort-order*))
		  sorts)
	    t
	    nil)))))

(defun print-terletox (x)
  (format t "~&term = ")
  (term-print (caar x) t t)
  ;; (print-chaos-object (caar x))
  (format t ", prec=~d" (cdar x))
  (format t ", tokens=") (print-chaos-object (cdr x)))

(defun print-terletox-list (x)
  (dolist (y x)
    (print-terletox y)))

;;; PARSER-MAKE-APPLFORM sort method arg-list
;;; make application form.
;;;
;;;  ** fill missing attributes by a variable for record/class instances if
;;;     required. also generaizes the pattern, that is, replaces class/record
;;;     id by a variable, and attributes' ids by variables.
;;;  NOTE: 
;;;
;;;  (block find-instance
;;;    (when (or (eq method *object-reference-method*)
;;;              (method-is-restriction-of method *object-reference-method*))
;;;      (let ((id (car arg-list))
;;;            (class (sort-id sort))
;;;            (object nil))
;;;        (when (term-is-variable? id)
;;;          (return-from find-instance nil))
;;;        (when (setf object (find-instance id class))
;;;          (return-from parser-make-applform object)))))
;;;

(defvar *rc-debug* nil)

(defun parser-make-applform (sort method arg-list)
  (declare (type sort* sort)
	   (type method method)
	   (type list arg-list))
  (macrolet ((not-lowest-p-fast (sort)
	       `(or (eq ,sort *universal-sort*)
		    (eq ,sort *huniversal-sort*)
		    (eq ,sort *cosmos-sort*)
		    (eq (sort-type ,sort) '%err-sort))))
    (flet ((make-form (sort method arg-list)
	     (make-applform sort method arg-list)))
      (let ((result nil))
	(if *fill-rc-attribute*
	    (let ((attrpos nil)
		  (class nil))
	      (if (method-is-object-constructor method)
		  (progn (setf attrpos 2) (setf class t))
		(when (method-is-record-constructor method)
		  (setf attrpos 1)))
	      (if attrpos
		  (let ((attrs (nth attrpos arg-list))
			(cr-sort (method-coarity method)))
		    (when class
		      (replace-class-id-with-var cr-sort arg-list))
		    (if attrs
			(cond ((sort= (term-sort attrs) *attribute-list-sort*)
			       (let* ((attr-method (term-head attrs))
				      (sv-pairs (list-ac-subterms attrs
								  attr-method))
				      (flg nil))
				 (dolist (sv-pair sv-pairs)
				   (block next
				     (when (sort= (term-sort sv-pair)
						  *attribute-list-sort*)
				       (setf flg t)
				       (return-from next nil))
				     ;; normal sv-pair
				     (replace-attr-id-with-var cr-sort sv-pair)))
				 (unless flg
				   (when (or *parsing-axiom-lhs*
					     *parse-lhs-attr-vars*)
				     ;; (break "1")
				     (setq *parse-lhs-attr-vars* t)
				     (setf (nth attrpos arg-list)
				       (make-right-assoc-normal-form
					attr-method
					(nconc sv-pairs
					       (list
						*attribute-list-aux-variable*))))))
				 (setq result (make-form sort method arg-list))
				 result))
			      (t ;; single sv-pair & not list of attribure.
			       (replace-attr-id-with-var cr-sort attrs)
			       (when (or *parsing-axiom-lhs*
					 *parse-lhs-attr-vars*)
				 ;; (break "2")
				 (setq *parse-lhs-attr-vars* t)
				 (setf (nth attrpos arg-list)
				   (make-applform
				    *attribute-list-sort*
				    *attribute-list-constructor*
				    (list attrs
					  *attribute-list-aux-variable*))))
			       (setq result (make-form sort method arg-list))
			       result))
		      ;; no attributes
		      (progn
			(setq result (make-form sort method arg-list))
			)))
		(progn
		  (setq result (make-form sort method arg-list))
		  )))
	  ;; normal term
	  (setq result (make-form sort method arg-list)))
	;; special treatment of if_then_else_fi
	;; special treatment of generic operators
	(when (eq (term-head result) *bool-if*)
	  (set-if-then-else-sort result))
	result))))

(defun replace-class-id-with-var (cr-sort arg-list)
  (declare (type sort* cr-sort)
	   (type list arg-list))
  (let ((class-id (second arg-list))
	(id-var nil))
    (unless (term-is-variable? class-id)
      (setf id-var (crsort-id-variable cr-sort))
      (unless id-var
	(with-output-panic-message ()
	  (format t "could not find Class id variable for class ~s"
		  (sort-id cr-sort))
	  ;; (break)
	  (chaos-error 'panic)))
      (if *parsing-axiom-lhs*
	  (pushnew id-var *lhs-attrid-vars*)
	  (unless (memq id-var *lhs-attrid-vars*)
	    (return-from replace-class-id-with-var nil)))
      ;;
      (setf (second arg-list) id-var))
    arg-list))

(defun replace-attr-id-with-var (cr-sort sv-pair)
  (declare (type sort* cr-sort)
	   (type term sv-pair))
  (let ((attr-id (term-arg-1 sv-pair))
	id-var)
    (unless (term-is-variable? attr-id)
      (setf id-var (get-attribute-id-variable
		    (car (method-symbol (term-method attr-id)))
		    cr-sort))
      (unless id-var
	(with-output-panic-message ()
	  (format t "could not find id variable for slot ~a of sort ~a"
		  (car (method-symbol (term-method attr-id)))
		  (sort-id cr-sort))
	  (print-next)
	  (princ "id term = ")
	  (term-print attr-id)
	  (print-next)
	  (princ " sv pair = ")
	  (print-chaos-object sv-pair)
	  ;; (break)
	  (chaos-error 'panic)
	  ))
      (if *parsing-axiom-lhs*
	  (pushnew id-var *lhs-attrid-vars*)
	  (unless (memq id-var *lhs-attrid-vars*)
	    (return-from replace-attr-id-with-var nil)))
      ;;
      (setf (term-arg-1 sv-pair) id-var))
    sv-pair))

;;;  op are-argumentsorts-correct :
;;;       Operator
;;;       LIST[ Sort ]  -- possibly empty (cf. constants)
;;;       Module
;;;       -> Bool .
;;;
;;;  Abstract: predicate returning 't {true} if each sort in the list
;;;    (meant to be a list of argument sorts) is included in the sort
;;;    expected by the operator for an argument at this position.
;;;
#||
*identical*        ===
*nonidentical*     =/==
*bool-if*   if_then_else_fi
*bool-equal* ==
*beh-equal*  =*=
*bool-nonequal* =/=
*beh-eq-pred* =b=
*rwl-predicate* ==>
*rwl-predicate2* =()=>
*sort-membership* _:_
||#
;;; !!! to optimize !!!
(defun are-argumentsorts-correct (method sort-list module)
  (declare (type method method)
	   (type list sort-list)
	   (type module module))
  (if (null sort-list)
      t
    (if (check-universally-defined-builtins method sort-list module)
	(let* ((reference-sort-list (method-arity method))
	       (sort-order (module-sort-order module))
	       (result t)
	       (sort-list-prime sort-list)
	       (sort nil))
	  (dolist (reference-sort reference-sort-list result)
	    (setq sort (car sort-list-prime)
		  sort-list-prime (cdr sort-list-prime)) ;for next iteration
	    (if (or (sort= reference-sort *universal-sort*)
		    (sort= reference-sort *huniversal-sort*)
		    (sort= reference-sort *cosmos*)
		    (err-sort-p reference-sort)
		    (sort<= sort reference-sort sort-order))
		;;then do nothing; go to next iteration:
		nil
	      ;; else abort looping; return false:
	      (progn
		(when *on-parse-debug*
		  (format t "~&incorrect argument sort ~a" (sort-id sort)))
		(return nil)))))
      nil)))

(defun arity-contains-universal-sort (method)
  (if (cdr (method-arity method))
      (and (or (eq method *bool-if*)
	       (dolist (s (method-arity method) t)
		 (unless (or (eq s *cosmos*)
			     (eq s *universal-sort*)
			     (eq s *huniversal-sort*))
		   (return-from arity-contains-universal-sort nil))))
	   ;;(every #'(lambda (x y) (eq x y)) (method-arity method))
	   )
    nil))

(defun check-universally-defined-builtins (method sort-list module)
  (let ((so (module-sort-order module)))
    (if ;; (memq method *bi-universal-operators*)
	(arity-contains-universal-sort method)
	(cond ((eq method *bool-if*)
	       ;; if_then_else_fi
	       (parser-in-same-connected-component (second sort-list)
						   (third sort-list)
						   so))
	      #||
	      ((eq method *rwl-predicate2*)
	       ;; _=()=>_
	       (parser-in-same-connected-component (first sort-list)
						   (third sort-list)
						   so))
	      ||#
	      ((eq method *sort-membership*)
	       ;; _:is_, the first argument is a term and the second
	       ;; argument is built-in constant of SortId.
	       ;; thus, anyhing is OK. 
	       t)
	      (t
	       ;; other binary universal operators
	       (parser-in-same-connected-component (first sort-list)
						   (second sort-list)
						   so)))
	t)))

;;;  op are-well-defined-terms :
;;;       LIST[ ChaosTerm ]  -- possibly empty
;;;       -> Bool .

;;;  Abstract: predicate returning 't {true} if all terms are well-formed.

(defun are-well-defined-terms (chaos-term-list)
  (declare (type list chaos-term-list))
  (let ((result t))
    (dolist (chaos-term chaos-term-list result)
      (if (term-ill-defined chaos-term)
	  ;; abort looping and return false
	  (return nil)))))


;;; EOF

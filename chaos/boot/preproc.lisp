;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: preproc.lisp,v 1.10 2010-08-04 04:37:34 sawada Exp $
(in-package :chaos)
#|==============================================================================
				 System: Chaos
				  Module: boot
			       File: preproc.lisp
==============================================================================|#

;;;*****************************************************************************
;;; 				Support procs of
;;; 			OBJ compatible Standard Prelude
;;;				       +
;;;			 Chaos specific builtin modules
;;;*****************************************************************************

;;;-----------------------------------------------------------------------------
;;; module UNIVERSAL
;;;-----------------------------------------------------------------------------
;;(defun install-Universal ()
;;  (let ((UNIVERSAL (eval-modexp "UNIVERSAL")))
;;    (setf *universal-sort*
;;          (find-sort-in UNIVERSAL "Universal"))
;;    (setf *match-dep-var* (make-variable-term *universal-sort* 'REST))
;;    ))

;;; module PARSER
;;;-----------------------------------------------------------------------------
(defun token-is-sort-id (token)
  (and (stringp token)
       (<= 1 (length token))
       (find-all-sorts-in (or *current-module* *last-module*)
			  token)))
(defun create-sort-id (token) token)
(defun print-sort-id (x) (princ x))
(defun is-sort-Id (x)
  (token-is-sort-id x))

;;;-----------------------------------------------------------------------------
;;; module IDENTICAL
;;;-----------------------------------------------------------------------------

;;; setup-identical
#||
(defun setup-identical ()
  (let ((id-opinfo nil)
	(nid-opinfo nil))
    (setf *IDENTICAL-module* (eval-modexp "IDENTICAL"))
    (with-in-module (*identical-module*)
      (setf id-opinfo (find-operator '("_" "===" "_")
				     2
				     *identical-module*))
      (setf *identical*
	  (lowest-method* (car (opinfo-methods id-opinfo))))
      (setf nid-opinfo (find-operator '("_" "=/==" "_") 2 *identical-module*))
      (setf *nonidentical*
	    (lowest-method* (car (opinfo-methods nid-opinfo))))
      )))
||#

;;;-----------------------------------------------------------------------------
;;;  module NZNAT
;;;-----------------------------------------------------------------------------
(defun is-NzNat-token (token)
  (and (stringp token)
       (every #'digit-char-p token)
       (some #'(lambda (ch) (not (eql #\0 ch))) token)))
(defun create-NzNat (token) (read-from-string token))
(defun is-NzNat (x) (and (integerp x) (< 0 x)))

;;;-----------------------------------------------------------------------------
;;; module NAT
;;;-----------------------------------------------------------------------------
(defun is-Zero-token (x) (equal "0" x))
(defun create-Zero (x) (declare (ignore x)) 0)
(defun is-Zero (x) (= 0 x))

(defun is-Nat-token (token) (declare (ignore token)) nil)
(defun create-Nat (token) (read-from-string token))
(defun is-Nat (x) (and (integerp x) (<= 0 x)))

;;;-----------------------------------------------------------------------------
;;; module INT
;;;-----------------------------------------------------------------------------
(defun is-NzInt-token (token)
  (and (stringp token)
       (general-read-numberp token)
       (<= 2 (length token))
       (eql #\- (char token 0))
       (some #'(lambda (ch) (not (eql #\0 ch))) token)))
(defun create-NzInt (x) (read-from-string x))
(defun is-NzInt (x) (and (integerp x) (not (= 0 x))))

(defun create-Int (token) (read-from-string token))
(defun is-Int-token (tok) (declare (ignore tok)) nil)
(defun print-Int (x) (prin1 x))
(defun is-Int (x) (integerp x))

;;;-----------------------------------------------------------------------------
;;; module RAT
;;;-----------------------------------------------------------------------------
(defun is-NzRat-token (token)
  (and (stringp token)
       (every #'(lambda (x)
           (or (digit-char-p x)
	       (eql #\- x)
	       (eql #\/ x)))
	 token)
       (let* ((first (if (eql #\- (char token 0)) 1 0))
	      (slash (position #\/ token)))
	 (and slash
	      (is-NzNat-token (subseq token first slash))
	      (is-NzNat-token (subseq token (+ slash 1)))))))
(defun create-NzRat (x) (read-from-string x))
(defun is-NzRat (x) (and (rationalp x) (not (= 0 x))))

(defun is-Rat-token (tok) (declare (ignore tok)) nil)
(defun create-Rat (x) (read-from-string x))
(defun RAT-print (x)
  (if (typep x 'ratio)
      (progn (prin1 (numerator x)) (princ "/") (prin1 (denominator x)))
    (prin1 x)))

;;;-----------------------------------------------------------------------------
;;; module ID
;;;-----------------------------------------------------------------------------
(defun is-Id-token (token)
  (and (stringp token)
       (<= 1 (length token))
       (alpha-char-p (char token 0))
       ))
(defun create-Id (token) (intern token))
(defun print-Id (x) (princ (string x)))
(defun is-Id (x)
  (and (symbolp x)
       (is-Id-token (symbol-name x))))

;;;-----------------------------------------------------------------------------
;;; module QID 
;;;-----------------------------------------------------------------------------
(defun is-qId-token (token)
  (and (stringp token)
       (<= 2 (length token))
       (eql #\' (char token 0))
       (alpha-char-p (char token 1))
       ))
(defun create-qId (token) (intern (subseq token 1)))
(defun print-qId (x) (format t "'~a" x))
(defun is-qId (x)
  (and (symbolp x)
       (is-Id-token (symbol-name x))))

;;;-----------------------------------------------------------------------------
;;; module FLOAT
;;;-----------------------------------------------------------------------------
(defun is-Float-token (token)
  (and (stringp token)
       (or (digit-char-p (char token 0))
	   (and (member (char token 0) '(#\+ #\. #\-))
		(<= 2 (length token))
		(digit-char-p (char token 1))))
       (multiple-value-bind (res len) (read-from-string token)
	 (declare (ignore res))
	 (and (= (length token) len)
	      (member (type-of (read-from-string token))
		      '(float long-float short-float fixnum bignum ratio
			single-float double-float
	     ))))))
(defun create-Float (token)
  (coerce (read-from-string token) 'long-float))
(defun print-Float (val) (prin1 val))
(defun is-Float (val) (typep val 'float))

;;;-----------------------------------------------------------------------------
;;; ChaosValue Builtin Sort
;;;-----------------------------------------------------------------------------
(defmacro is-compiled-chaos-value (_val)
  `(and (consp ,_val)
	(eq (car ,_val) '|%Chaos|)))

(defun print-chaos-value (val)
  #||
  (format t "#% ~s"
	  (if (is-compiled-chaos-value val)
	      (nth 2 val)
	    val))
  ||#
  (print-chaos-object val)
  )

(defun is-variable? (val)
  (and (is-term? val) (term-is-variable? val)))

(defun is-applform? (val)
  (and (is-term? val) (term-is-applform? val)))

(defun is-pvariable? (val)
  (and (is-term? val) (term-is-psuedo-constant? val)))

(defun is-lisp-form? (val)
  (and (is-term? val) (term-is-lisp-form? val)))

(defun is-slisp-form? (val)
  (and (is-term? val) (term-is-simple-lisp-form? val)))

(defun is-glisp-form? (val)
  (and (is-term? val) (term-is-general-lisp-form? val)))

(defun is-bconst-term? (val)
  (and (is-term? val) (term-is-builtin-constant? val)))

;;;-----------------------------------------------------------------------------
;;; TRUTH-VALUE, TRUTH & BOOL
;;;-----------------------------------------------------------------------------
;;;
(defun setup-truth-value ()
  (setq *truth-value-module* (eval-modexp "TRUTH-VALUE"))
  (prepare-for-parsing *truth-value-module*)
  (with-in-module (*truth-value-module*)
    (setq *bool-sort*
	  (find-sort-in *truth-value-module* "Bool"))
    (let* ((t-opinfo (find-operator '("true") 0 *truth-value-module*))
	   (f-opinfo (find-operator '("false") 0 *truth-value-module*))
	   (t-meth (lowest-method* (car (opinfo-methods t-opinfo))))
	   (f-meth (lowest-method* (car (opinfo-methods f-opinfo)))))
      (setq *BOOL-true* (make-applform *bool-sort*
				       t-meth
				       nil))
      (setq *bool-true-meth* t-meth)
      (setq *bool-false* (make-applform *bool-sort*
					f-meth
					nil))
      (setq *bool-false-meth* f-meth))
    ))
      
#||
(defun setup-truth ()
  (setq *TRUTH-module* (eval-modexp "TRUTH"))
  (prepare-for-parsing *truth-module*)
  (with-in-module (*truth-module*)
    (let* ((sort-mem-op-info (find-operator '("_" ":is" "_")
					    2
					    *truth-module*))
	   (sort-mem-meth (lowest-method* (car (opinfo-methods sort-mem-op-info)))))
      (setq *sort-membership* sort-mem-meth))
    
    (let* ((if-op-info (find-operator '("if" "_" "then" "_" "else" "_" "fi")
				      3
				      *truth-module*))
	   (if-meth (lowest-method* (car (opinfo-methods if-op-info)))))
      (setq *BOOL-if* if-meth)
      ;; 
      (let* ((equal-op-info (find-operator '("_" "==" "_") 2 *truth-module*))
	     (equal-meth (lowest-method* (car (opinfo-methods equal-op-info))))
	     (beq-op-info (find-operator '("_" "=*=" "_") 2 *truth-module*))
	     (beq-meth (lowest-method* (car (opinfo-methods beq-op-info))))
	     (n-equal-op-info (find-operator '("_" "=/=" "_") 2 *truth-module*))
	     (n-equal-meth (lowest-method* (car (opinfo-methods n-equal-op-info))))
	     (beh-eq-info (find-operator '("_" "=b=" "_") 2 *truth-module*))
	     (beh-eq-meth (lowest-method* (car (opinfo-methods beh-eq-info)))))
	(setq *bool-equal* equal-meth)
	(setq *beh-equal* beq-meth)
	(setq *bool-nonequal* n-equal-meth)
	(setq *beh-eq-pred* beh-eq-meth)
	))))
||#

#||
(defun setup-bool ()
  (setq *BOOL-module* (eval-modexp "BOOL"))
  (with-in-module (*bool-module*)
    (let* ((and-op-info (find-operator '("_" "and" "_") 2 *bool-module*))
	   (and-meth (lowest-method* (car (opinfo-methods and-op-info)))))
      (setq *bool-and* and-meth))
    (let* ((or-op-info (find-operator '("_" "or" "_") 2 *bool-module*))
	   (or-meth (lowest-method* (car (opinfo-methods or-op-info)))))
      (setq *bool-or* or-meth))
    (let* ((not-op-info (find-operator '("not" "_") 1 *bool-module*))
	   (not-meth (lowest-method* (car (opinfo-methods not-op-info)))))
      (setq *bool-not* not-meth))
    (let* ((xor-op-info (find-operator '("_" "xor" "_") 2 *bool-module*))
	   (xor-meth (lowest-method* (car (opinfo-methods xor-op-info)))))
      (setq *bool-xor* xor-meth))
    (let* ((imp-op-info (find-operator '("_" "implies" "_") 2 *bool-module*))
	   (imp-meth (lowest-method* (car (opinfo-methods imp-op-info)))))
      (setq *bool-imply* imp-meth))
    (let* ((and-also (find-operator '("_" "and-also" "_") 2 *bool-module*))
	   (and-also-meth (lowest-method* (car (opinfo-methods and-also)))))
      (setq *bool-and-also* and-also-meth))
    (let* ((or-else (find-operator '("_" "or-else" "_") 2 *bool-module*))
	   (or-else-meth (lowest-method* (car (opinfo-methods or-else)))))
      (setq *bool-or-else* or-else-meth))
    (let* ((iff (find-operator '("_" "iff" "_") 2 *bool-module*))
	   (iff-meth (lowest-method* (car (opinfo-methods iff)))))
      (setq *bool-iff* iff-meth))
      
    ))

||#

;;; op bool-make-conjunction : Term Term -> Term
;;;
(defun BOOL-make-conjunction (t1 t2)
  (make-applform *bool-sort* *bool-and* (list t1 t2)))

;;; op coerce-to-Bool : Lisp -> Bool
;;;
(defun coerce-to-Bool (x)
  (if x *BOOL-true* *BOOL-false*))

;;; INSTALL-TRUTH
;;;
#|| ^^^ not used
(defun install-truth ()
  (final-setup *truth-module*))
||#

;;;-----------------------------------------------------------------------------
;;; QID
;;;-----------------------------------------------------------------------------
(defun setup-qid ()
  (setq *qid-module* (eval-modexp "QID"))
  (final-setup *qid-module*)
  (with-in-module (*qid-module*)
    (setq *qid-sort* (find-sort-in *qid-module* "Id"))))

;;;-----------------------------------------------------------------------------
;;; module RWL
;;;-----------------------------------------------------------------------------

#||
(defun setup-rwl ()
  (setq *rwl-module* (eval-modexp "RWL"))
  (final-setup *rwl-module*)
  (with-in-module (*rwl-module*)
    (let* ((nat-star (find-sort-in *rwl-module* "Nat*"))
	   (rwl-op-info (find-operator '("_" "==>" "_") 2 *rwl-module*))
	   (rwl-pred (lowest-method* (car (opinfo-methods rwl-op-info))))
	   (rwl-op-info2 (find-operator '("_" "=" "(" "_" ")" "=>" "_")
					3
					*rwl-module*))
	   (rwl-pred2 (lowest-method* (car (opinfo-methods rwl-op-info2)))))
      (unless nat-star
	(with-output-panic-message ()
	  (princ "could not find sort Nat*...")
	  (break)))
      (unless rwl-pred
	(with-output-panic-message ()
	  (princ "could not find ==> operaotr....")
	  (break)))
      (unless rwl-pred2
	(with-output-panic-message ()
	  (print "could not find =(?)=> operator ....")
	  (break)))
      ;;
      (setq *rwl-nat-star-sort* nat-star)
      (setq *rwl-predicate* rwl-pred)
      (setq *rwl-predicate2* rwl-pred2))
    ))
||#

;;;-----------------------------------------------------------------------------
;;; module CHARACTER
;;;-----------------------------------------------------------------------------

;;; INSTALL-CHARACTER

(defun install-character ()
  (let ((char-module (eval-modexp "CHAR-VALUE")))
    (if (and char-module (not (modexp-is-error char-module)))
	(let ((c-sort (find-sort-in char-module "Character")))
	  (if c-sort
	      (setq *character-sort* c-sort)
	      (with-output-panic-message ()
		(princ "could not find Character sort in module CHAR-VALUE"))))
	(with-output-panic-message ()
	  (princ "Could not find module CHAR-VALUE.")
	  (break)))))

;;; character-token ::= 'char'
;;;            char ::= <alphanumeric>
;;;
(defun is-character-token (tok)
  (and (stringp tok)
       (let ((len (length tok)))
	 (and (< 2 len)
	      (eql (char tok 0) #\')
	      (eql (char tok (1- len)) #\')
	      (let ((first-char (char tok 1)))
		(case first-char
		  (#\\			; escape
		   (or (every #'(lambda (x) (digit-char-p x)) (subseq tok 2 (1- len)))
		       (= len 4)))
		  (t (= len 3))))))))

(defun create-character (tok)
  (let ((len (length tok)))
    (if (= 3 len)
	(char tok 1)
	(let ((first-char (char tok 2)))
	  (if (digit-char-p first-char)
	      (let ((num (read-from-string (subseq tok 2 (1- len)))))
		(if (< num char-code-limit)
		    (code-char num)
		    (with-output-chaos-error ('invalid-char-code)
		      (format t "invalid character code '\\~d' is given" num)
		      )))
	      (case first-char
		(#\n #\newline)
		(#\l #\linefeed)
		(#\t #\tab)
		(#\s #\space)
		(#\p #\page)
		(otherwise first-char)))))))

(defun is-character (obj) (characterp obj))

(defun print-character (obj)
  (if (graphic-char-p obj)
      (if (eql obj #\space)
	  (princ "'\\s'")
	  (format t "'~a'" obj))
      (case obj
	(#\newline (princ "'\\n'"))
	;; #-:CLISP (#\linefeed (princ "'\\l'"))
	(#\tab (princ "'\\t'"))
	(#\space (princ "'\\s'"))
	(#\page (princ "'\\p'"))
	(otherwise (format t "'\\~d'" (char-code obj))))))
      
;;;-----------------------------------------------------------------------------
;;; module STRING
;;;-----------------------------------------------------------------------------
(defun install-string ()
  (let ((string-module (eval-modexp "STRING-VALUE")))
    (if (and string-module (not (modexp-is-error string-module)))
	(let ((s-sort (find-sort-in string-module "String")))
	  (if s-sort
	      (setq *string-sort* s-sort)
	      (with-output-panic-message()
		(princ "could not find String sort in module STRING-VALUE"))))
	(with-output-panic-message()
	  (princ "Could not find module STRING-VALUE.")
	  (break)))))

;;;-----------------------------------------------------------------------------
;;; module CHAOS:EXPR
;;;-----------------------------------------------------------------------------
(defun install-chaos-expr ()
  (let ((module (eval-modexp "CHAOS:EXPR")))
    (labels ((sort-missing (sort-name)
	       (with-output-panic-message ()
		 (format t "missing sort ~s" sort-name))))
      (macrolet ((set-sort (sym s-name)
		   `(or (setq ,sym (find-sort-in module ,s-name))
			(sort-missing ,s-name))))
      (if (and module (not (modexp-is-error module)))
	  (progn
	    (final-setup module)
	    (set-sort *chaos-value-sort* "ChaosExpr")
	    (set-sort *sort-sort* "ChaosSort")
	    (set-sort *general-sort* "Sort")
	    (set-sort *and-sort* "AndSort")
	    (set-sort *or-sort* "OrSort")
	    (set-sort *err-sort* "ErrSort")
	    (set-sort *operator-sort* "Operator")
	    (set-sort *axiom-sort* "Axiom")
	    (set-sort *module-sort* "Module")
	    (set-sort *term-sort* "Term")
	    (set-sort *variable-sort* "Variable")
	    (set-sort *appl-form-sort* "ApplForm")
	    (set-sort *pvariable-sort* "PVariable")
	    (set-sort *lisp-term-sort* "LispTerm")
	    (set-sort *slisp-term-sort* "SlispTerm")
	    (set-sort *glisp-term-sort* "GlispTerm")
	    (set-sort *bconst-term-sort* "BconstTerm")
	    (set-sort *optheory-sort* "OpTheory")
	    (set-sort *modexpr-sort* "ModExpr")
	    (set-sort *chaos-list-sort* "ChaosList")
	    (set-sort *chaos-void-sort* "ChaosVoid")
	    #||
	    (declare-subsort-in-module
	     `((,*general-sort* ,*and-sort* ,*or-sort* ,*err-sort*
				:< ,*sort-sort*)
	       (,*sort-sort* ,*operator-sort* ,*axiom-sort* ,*module-sort*
			     ,*term-sort* ,*modexpr-sort* ,*string-sort*
			     ,*qid-sort* ,*chaos-list-sort*
			     :< ,*chaos-value-sort*)
	       (,*chaos-void-sort* :< ,*general-sort* ,*and-sort* ,*or-sort* ,*err-sort*
				   ,*operator-sort* ,*axiom-sort*
				   ,*module-sort* ,*term-sort* ,*modexpr-sort*
				   ,*chaos-list-sort*))
	     module)
	    ||#
	    )
	(with-output-panic-message()
	  (princ "Could not find module ChaosExpr.")
	  (break)))))))

;;;-----------------------------------------------------------------------------
;;; Record Structure/Object
;;;-----------------------------------------------------------------------------

;;; OBJECT ID
;;;
(defun install-object-id ()
  (let ((oid-mod (eval-modexp "OBJECT-ID")))
    (when (or (null oid-mod) (modexp-is-error oid-mod))
      (with-output-panic-message ()
	(princ "OBJECT-ID is missing!.")
	(break)))
    (let ((oid-sort (find-sort-in oid-mod "ObjectId")))
      (unless oid-sort (with-output-panic-message ()
			 (princ "sort ObjectId missing!.")
			 (chaos-to-top)))
      (setq *object-identifier-sort* oid-sort))))

;;;
;;; RECORD/OBJECT
;;;
(defun install-record-object ()
  (let ((av-pair (eval-modexp "AVPAIR"))
	(rs (eval-modexp "RECORD-STRUCTURE"))
	(ob (eval-modexp "OBJECT"))
	(con (eval-modexp "STATE-CONFIGURATION"))
	(acz-con (eval-modexp "ACZ-CONFIGURATION")))
    (if (and av-pair (not (modexp-is-error av-pair)))
	(let ((attrid (find-sort-in av-pair "AttrId"))
	      (attrval (find-sort-in av-pair "AttrValue"))
	      (attribute (find-sort-in av-pair "Attribute"))
	      (attribute-list (find-sort-in av-pair "Attributes")))
	  (if attrid
	      (setf *attribute-id-sort* attrid)
	      (with-output-panic-message ()
		(princ "Panic: could not find sort AttrId")
		(break)))
	  (if attrval
	      (setf *attr-value-sort* attrval)
	      (with-output-panic-message ()
		(princ "Panic: counld not find sort AttrValue")
		(break)))
	  (if attribute
	      (setf *attribute-sort* attribute)
	      (with-output-panic-message ()
		(princ "Panic: could not find sort Attribute")
		(break)))
	  (if attribute-list
	      (progn (setf *attribute-list-sort* attribute-list)
		     (setf *attribute-list-aux-variable*
			   (make-variable-term *attribute-list-sort*
					       '|Attr_Aux|)))
	      (with-output-panic-message ()
		(princ "could not find sort Attributes")
		(break)))
	  (let ((attr-constructor (find-method-in av-pair
						  '("_" "=" "_")
						  (list *attribute-id-sort*
							*attr-value-sort*)
						  *attribute-sort*))
		(atlist-constructor (find-method-in av-pair
						    '("_" "," "_")
						    (list *attribute-list-sort*
							  *attribute-list-sort*)
						    *attribute-list-sort*)))
	    (if attr-constructor
		(setf *attribute-constructor* attr-constructor)
		(with-output-panic-message ()
		  (princ "could not find attribute constructor!")
		  (break)))
	    (if atlist-constructor
		(setf *attribute-list-constructor* atlist-constructor)
		(with-output-panic-message ()
		  (princ "could not find attribute list constructor!")
		  (break))))
	  )
	(with-output-panic-message ()
	  (princ "could not find module AVPAIR")))
    (if rs
	(let ((rinst (find-sort-in rs "RecordInstance"))
	      (rid (find-sort-in rs "RecordId"))
	      (constr nil)
	      void)
	  (if rinst
	      (setf *record-instance-sort* rinst)
	      (with-output-panic-message ()
		(princ "could not find RecordInstance sort!!")))
	  (if rid
	      (setf *record-id-sort* rid)
	      (error "Panic: could not find sort RecordId"))
	  (setf constr  (find-method-in rs
					'("_" "{" "_" "}")
					(list *record-id-sort*
					      *attribute-list-sort*)
					*record-instance-sort*))
	  (if constr
	      (progn (setf *record-constructor-method* constr)
		     (setf *record-constructor-op*
			   (method-operator constr (module-opinfo-table rs))))
	      (error "Panic: could not find record constructor!"))
	  (setf void (find-method-in rs '("*VoidRecord*") nil *record-instance-sort*))
	  (if void
	      (setf *void-record*
		    (make-applform-simple *record-instance-sort* void))
	      (error "Panic: could not find void record operator."))
	  )
	(error "Panic: could not find module RECORD-STRUCTURE"))
    (if ob
	(let ((obj (find-sort-in ob "Object"))
	      (cid (find-sort-in ob "ClassId"))
	      (msg (find-sort-in ob "Message"))
	      ref
	      void
	      constr)
	  (if obj
	      (setq *object-sort* obj)
	      (error "Panic: could not find sort Object"))
	  (if cid
	      (setf *class-id-sort* cid)
	      (error "Panic: could not find sort ClassId"))
	  (if msg
	      (setf *message-sort* msg)
	      (error "Panic: could not find sort Message"))
	  (setf void (find-method-in ob '("*VoidObject*") nil *object-sort*))
	  (if void
	      (setf *void-object*
		    (make-applform-simple *object-sort* void))
	      (error "Panic: could not find void object operator."))
	  (setf ref (find-method-in ob
				    '("<" "_" ":" "_" ">")
				    (list *object-identifier-sort*
					  *class-id-sort*)
				    *object-sort*))
	  (if ref
	      (setf *object-reference-method* ref)
	      (error "Panic: could not find object reference method."))
	  (setf constr (find-method-in ob
				       '("<" "_" ":" "_" "|" "_" ">")
				       (list *object-identifier-sort*
					     *class-id-sort*
					     *attribute-list-sort*)
				       *object-sort*))
	  (if constr
	      (progn (setf *object-constructor-method* constr)
		     (setf *object-constructor-op*
			   (method-operator constr (module-opinfo-table ob))))
	      (error "Panic: could not find object constructor method."))
	  )
	(error "Panic: could not find module OBJECT"))
    (if con
	(let ((config (find-sort-in con "Configuration")))
	  (if config
	      (setf *configuration-sort* config)
	      (error "Panic: could not find sort Configuration")))
	(error "Panic: could not find module STATE-CONFIGURATION"))
    (if acz-con
	(let ((acz-config (find-sort-in acz-con "ACZ-Configuration")))
	  (if acz-config
	      (setf *acz-configuration-sort* acz-config)
	      (error "Panic: could not find sort ACZ-Configuration")))
	(error "Panic: could not find module ACZ-CONFIGURATION"))))

;;; EOF

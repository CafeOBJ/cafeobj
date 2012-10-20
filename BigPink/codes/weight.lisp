;;;-*-Mode:LISP; Package: CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: weight.lisp,v 1.2 2003-11-04 03:11:25 sawada Exp $
;;;
(in-package :chaos)
#|=============================================================================
			     System:Chaos
			    Module:BigPink
			   File:weight.lisp
=============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; **************************************************************
;;; functions to weight clauses, literals and terms
;;; (also some routines handling lexical ordering (not LRPO)).
;;; **************************************************************

;;; extend module info
;;; :op-lex
;;; contains operator symbol precedence list defined by "lex" command.
;;;
(defmacro module-op-lex (_mod)
  `(getf (object-misc-info ,_mod) :op-lex))

;;; OPERATOR PREC TABLE
;;;
(defvar .op-lex-relation-table. (make-hash-table :test #'eq))
(defvar *debug-op-relation* nil)

;;; OP-RELATION
;;; (op sub-operators super-operators)
(defmacro make-op-relation (_op &optional _sub _super)
  `(list ,_op ,_sub ,_super))

(defmacro get-op-relation (_op _order) `(gethash ,_op ,_order))
(defmacro op-relation-op (_sl) `(car ,_sl))
(defmacro _subops (_sl) `(cadr ,_sl))
(defmacro _superops (_sl) `(caddr ,_sl))
(defmacro subops (_op &optional (_order '.op-lex-relation-table.))
  `(_subops (get-op-relation ,_op ,_order)))
(defmacro superops (_op &optional (_order '.op-lex-relation-table.))
  `(_superops (get-op-relation ,_op ,_order)))

(declaim (inline op-lex<))

(defun op-lex< (op1 op2 &optional (order .op-lex-relation-table.))
  (declare (type method op1 op2)
	   (type hash-table .op-lex-relation-table.)
	   (values boolean))
  (memq op2 (superops op1 order)))

(defun dump-op-lex-relation-table ()
  (maphash #'(lambda (op rel)
	       (with-output-msg ()
		 (format t "operator ~a " op)
		 (print-method op)
		 (print-next)
		 (format t "subs: ~{~a~}"
			 (_subops rel))
		 (print-next)
		 (format t "supers: ~{~a~}"
			 (_superops rel))
		 (print-next)))
	   .op-lex-relation-table.))

(defun term-sub-operators (term)
  (declare (type term)
	   (values list))
  (let ((res nil))
    (declare (type list res))
    (when (term-is-application-form? term)
      (dolist (sub (term-subterms term))
	(when (term-is-application-form? sub)
	  (pushnew (term-head sub) res :test #'eq))))
    res))

;;; ADD-OP-TO-ORDER

(defun add-op-to-order (op &optional (order .op-lex-relation-table.))
  (declare (type method op)
	   (type hash-table .op-lex-relation-table.))
  (let ((ent (get-op-relation op order)))
    (unless ent
      (add-op-relation-to-order (make-op-relation op nil nil) order))))
  
;;; ADD-OP-RELATION-TO-ORDER op-relation operator-relation-table
;;; adds the op-relation to operator-relation-table
;;;
(defun gather-op-relations-from-order (relation
				       &optional
				       (order .op-lex-relation-table.))
  (declare (type list relation)
	   (type hash-table .op-lex-relation-table.)
	   (values list))
  (macrolet ((pushnew-relation (__?rel __?res)
	       ` (pushnew ,__?rel ,__?res :test #'eq)))
    (let ((res nil)
	  (op (op-relation-op relation))
	  (subs (_subops relation))
	  (sups (_superops relation)))
      (pushnew-relation (get-op-relation op order) res)
      (dolist (lops subs)
o	(pushnew-relation (get-op-relation lops order) res))
      (dolist (gops sups)
	(pushnew-relation (get-op-relation gops order) res))
      res)))

(defun add-op-relation-to-order (op-relation
				 &optional (order .op-lex-relation-table.))
  (let* ((op (op-relation-op op-relation))
	 (subs (_subops op-relation))
	 (supers (_superops op-relation)))
    (macrolet ((ls-union (_s _ls)
		 ` (let ((..sl (get-op-relation ,_s order)))
		     (pushnew ,_ls (_subops ..sl) :test #'eq)))
	       (gs-union (_s _gs)
		 ` (let ((..sl (get-op-relation ,_s order)))
		     (pushnew ,_gs (_superops ..sl) :test #'eq))))
      ;; merge new realtion
      (let ((o-op-rel (get-op-relation op order)))
	(if o-op-rel
	    (progn
	      (setf (_subops o-op-rel)
		    (union subs (_subops o-op-rel) :test #'eq))
	      (setf (_superops o-op-rel)
		    (union supers (_superops o-op-rel) :test #'eq)))
	    (progn
	      (setf (get-op-relation op order) op-relation)
	      (setf o-op-rel op-relation
		    subs (_subops op-relation)
		    supers (_superops op-relation)))))
      ;; we must gather relations which can be affected by new relation,
      ;; then compute transitive relations among them.
      (let ((rels (gather-op-relations-from-order op-relation order)))
	(declare (type list rels))
	(dolist (sl rels)
	  (let ((nsubs (_subops sl))
		(nsups (_superops sl)))
	    (declare (type list nsubs nsups))
	    (dolist (s1 nsubs)
	      (dolist (s2 nsups)
		(ls-union s2 s1)
		  (gs-union s1 s2))))))
      order)))

;;; MAKE-OP-REC-RELATIONS
;;;
(defun make-op-prec-relations (module)
  (declare (type module module))
  (clrhash .op-lex-relation-table.)
  (let ((axs (module-all-equations module))
	(opinfos (module-all-operators module))
	;; (ordered nil)
	(num-ops 0)
	)
    (declare (type fixnum num-ops))
    (dolist (opinfo opinfos)
      (dolist (m (opinfo-methods opinfo))
	(add-op-to-order m)
	(incf num-ops)))
    (dolist (ax axs)
      (block next
	(let ((lhs (axiom-lhs ax))
	      (rhs (axiom-rhs ax))
	      (cond (axiom-condition ax)))
	  ;;
	  (unless (and (is-true? cond)
		       (term-is-application-form? rhs)
		       (not (rule-is-builtin ax)))
	    (return-from next nil))
	  ;;
	  (let ((meth1 (term-head lhs))
		;; (meth2 (term-head rhs))
		;; (rhs-methods (term-sub-operators rhs))
		(rhs-methods (term-operators rhs)))
	    ;;
	    (setq rhs-methods (delete meth1 rhs-methods))
	    ;;
	    (let ((rel1 (make-op-relation meth1 rhs-methods)))
	      (add-op-relation-to-order rel1))
	    (dolist (lower rhs-methods)
	      (let ((rel2 (make-op-relation lower nil (list meth1))))
		(add-op-relation-to-order rel2)))
	    ))))
    ;; check cyclicity
    (let ((err-p nil))
      (maphash #'(lambda (op op-relation)
		   (when (memq op (_subops op-relation))
		     (with-output-chaos-warning ()
		       (princ "cycle in operator lexical ordering: ")
		       (princ (method-name op)))
		     (setq err-p t)))
	       .op-lex-relation-table.)
      (when err-p
	(with-output-chaos-warning ()
	  (princ "failed to construct operator lexical orderings."))))
    ;;
    (when *debug-op-relation*
      (dump-op-lex-relation-table))
    ;;
    ;; ordered
    ))

;;;
;;; OPERATOR LEXICAL ORDERING (valued).
;;;
(defvar .op-lex-prec-table. (make-hash-table :test #'eq))

(defun dump-op-lex-table ()
  (let ((entries nil))
    (maphash #'(lambda (x y)
	       (push (cons x y) entries))
	   .op-lex-prec-table.)
    (setq entries (sort entries
			#'(lambda (x y)
			    (< (cdr x) (cdr y)))))
    (dolist (e entries)
      (format t "~%meth ~s, prec = ~s" (car e) (cdr e)))
    ))

(defun op-lex-compare (m1 m2)
  (declare (type method m1 m2)
	   (values symbol))
  (flet ((compare-lex (name1 name2)
	   (declare (type list name1 name2))
	   (let ((n1 (reduce #'(lambda (x y)
				 (concatenate 'string x y))
			     name1))
		 (n2 (reduce #'(lambda (x y)
				 (concatenate 'string x y))
			     name2)))
	     (declare (type simple-string n1 n2))
	     (if (string< n1 n2)
		 :less
	       (if (string= n1 n2)
		   :same
		 :greater)))))
    ;;
    (if (op-lex< m1 m2)
	:less
      (if (op-lex< m2 m1)
	  :greater
	;;
	(let* ((l1 (method-name m1))
	       (l2 (method-name m2))
	       (ar1 (cdr l1))
	       (ar2 (cdr l2)))
	  (declare (type fixnum ar1 ar2)
		   (type list l1 l2))
	  (if (< ar1 ar2)
	      (if (= 0 ar1)
		  :less			; m1 is constant
		(compare-lex (car l1) (car l2)))
	    (if (= ar1 ar2)
		(compare-lex (car l1) (car l2))
	      ;; ar1 > ar2
	      (if (= 0 ar2)		; m2 is constant
		  :greater
		(compare-lex (car l1) (car l2))))))
	))))

;;; METHOD-LEX-PREC
;;;
(declaim (inline method-lex-prec))

(defun method-lex-prec (meth)
  (if (is-skolem meth)
      (gethash :skolem .op-lex-prec-table.)
    (gethash meth .op-lex-prec-table.)))

(defsetf method-lex-prec (meth) (value)
  `(if (is-skolem ,meth)
       (setf (gethash :skolem .op-lex-prec-table.) ,value)
     (setf (gethash ,meth .op-lex-prec-table.) ,value)))

;;; 
;;;
;;;
(defun order-lex-op (m1 m2)
  (declare (type method m1 m2)
	   (values boolean))
  (labels ((compare-lex (name1 name2)
	     (declare (type list name1 name2))
	     (let ((n1 (reduce #'(lambda (x y)
				   (concatenate 'string x y))
			       name1))
		   (n2 (reduce #'(lambda (x y)
				   (concatenate 'string x y))
			       name2)))
	       (declare (type simple-string n1 n2))
	       (if (string< n1 n2)
		   :less
		 (if (string= n1 n2)
		     :same
		   :greater))))
	   (order-op ()
	     (let* ((l1 (method-name m1))
		    (l2 (method-name m2))
		    (ar1 (cdr l1))
		    (ar2 (cdr l2)))
	       (declare (type fixnum ar1 ar2)
			(type list l1 l2))
	       (if (< ar1 ar2)
		   (if (= 0 ar1)
		       :less		; m1 is constant
		     (compare-lex (car l1) (car l2)))
		 (if (= ar1 ar2)
		     (compare-lex (car l1) (car l2))
		   ;; ar1 > ar2
		   (if (= 0 ar2)	; m2 is constant
		       :greater
		     (compare-lex (car l1) (car l2))))))
	     ))
    ;;
    (let ((cmp (order-op)))
      (declare (type symbol cmp))
      (if (eq cmp :less)
	  t
	(if (eq cmp :greater)
	    nil
	  (sort< (method-coarity m1) (method-coarity m2)
		 *current-sort-order*)))))
  )

(defun make-lexical-prec-table (module &optional (pre-ordered nil))
  (declare (type module module)
	   (type list pre-ordered))
  (clrhash .op-lex-prec-table.)
  (let ((opinfos (module-all-operators module))
	(mlist nil))
    (with-in-module (module)
      (unless pre-ordered
	(setq pre-ordered '(:* :skolem)))
      (dolist (opinfo opinfos)
	(dolist (m (opinfo-methods opinfo))
	  (push m mlist)))
      (setq mlist (sort mlist #'order-lex-op))
      ;;
      (do* ((i 1)
	    (ml pre-ordered (cdr ml))
	    (meth (car ml) (car ml)))
	  ((endp ml))
	(declare (type fixnum i))
	(cond ((eq meth :*)
	       (do ((ml mlist (cdr ml)))
		   ((null ml))
		 (unless (method-lex-prec (car ml))
		   (setf (method-lex-prec (car ml)) (the fixnum (* 2 i)))
		   (incf i))))
	      (t (setf (method-lex-prec meth)
		   (the fixnum (* 2 i)))
		 (incf i)))
	))
    ;;
    (when *debug-op-relation*
      (dump-op-lex-table))
    ))

;;;
;;; MAKE-OP-LEX-PREC-TABLE
;;; 
(defun make-op-lex-prec-table (module)
  (clrhash .op-lex-relation-table.)
  (unless (module-op-lex module)
    (make-op-prec-relations module))
  (make-lexical-prec-table module (module-op-lex module))
  )

;;; op-lex-precedence : op1 op2 -> {:greater, :less, :same, nil}
;;;
(defun op-lex-precedence (meth1 meth2)
  (declare (type method meth1 meth2)
	   (values symbol))
  (when (method-w= meth1 meth2)
    (return-from op-lex-precedence :same))
  (if (and (method-is-constructor? meth1)
	   (not (method-is-constructor? meth2)))
      :less
    (if (and (not (method-is-constructor? meth1))
	     (method-is-constructor? meth2))
	:greater
      (if (op-lex< meth1 meth2)
	  :less
	(if (op-lex< meth2 meth1)
	    :greater
	  (let ((p1 (method-lex-prec meth1))
		(p2 (method-lex-prec meth2)))
	    (declare (type fixnum p1 p2))
	    (if	(> p1 p2)
		:greater
	      (if (< p1 p2)
		  :less
		:same)))))))
  )

;;; TERM-WEIGHT
;;;
(defun term-weight (term)
  (declare (type term term)
	   (values fixnum))
  ;; must check answer also : TODO
  (cond ((term-is-variable? term) 1)
	((term-is-lisp-form? term) 1)
	((term-is-builtin-constant? term) 1)
	((and (term-is-atom? term)
	      (null (term-subterms term)))
	 1)
	(t (let (
		 #||
		 (max (if (term-is-atom? term)
			  (pn-flag atom-wt-max-args)
			(pn-flag term-wt-max-args)))
		 ||#
		 (wt 0))
	     (declare (type fixnum wt))
	     (dolist (sub (term-subterms term))
	       (let ((w1 (term-weight sub)))
		 (declare (type fixnum w1))
		 #||
		 (if max
		     (when (> w1 wt)
		       (setq wt w1))
		   (incf wt w1))
		 ||#
		 (incf wt w1)
		 ))
	     (1+ wt)))))

;;; WEIGHT-LEX-ORDER : TERM1 TERM2 -> {:greater, :less, nil}
;;;
(defun weight-lex-order (t1 t2)
  (declare (type term t1 t2)
	   (values symbol))
  (let ((i1 (term-weight t1))
	(i2 (term-weight t2)))
    (declare (type fixnum i1 i2))
    (if (> i1 i2)
	:greater
      (if (< i1 i2)
	  :less
	(term-lex-order t1 t2)))))

;;; TERM-LEX-ORDER : TERM1 TERM2 -> {:greater, :less, nil}
;;;
(defun term-lex-order (t1 t2)
  (declare (type term t1 t2)
	   (values symbol))
  (when (sort< (term-sort t1) (term-sort t2) *current-sort-order*)
    (return-from term-lex-order :less))
  (when (sort< (term-sort t2) (term-sort t1) *current-sort-order*)
    (return-from term-lex-order :greater))
  ;;
  ;; same sort
  ;;
  (cond ((term-is-variable? t1)
	 (if (term-is-variable? t2)
	     (if (variable-eq t1 t2)
		 :same
		nil)			; incomparable
	   (if (occurs-in t1 t2)
	       :less
	     nil)))
	((term-is-variable? t2)
	 (if (occurs-in t2 t1)
	     :greater
	   nil))
	;;
	((term-is-application-form? t1)
	 (if (term-is-application-form? t2)
	     (if (method-is-of-same-operator (term-head t1)
					     (term-head t2))
		 ;; same op
		 (let ((ret-code :same))
		   (do ((t1-sub (term-subterms t1) (cdr t1-sub))
			(t2-sub (term-subterms t2) (cdr t2-sub)))
		       ((or (null t1-sub)
			    (not (eq ret-code :same)))
			ret-code)
		     (setq ret-code
		       (term-lex-order (car t1-sub) (car t2-sub)))))
	       ;; different op
	       (op-lex-precedence (term-head t1) (term-head t2)))
	   ))
	((term-is-application-form? t2)
	 :less)
	(t :greater)
	))

(defun term-lex-order-vars (t1 t2)
  (declare (type term t1 t2)
	   (values symbol))
  (when (sort< (term-sort t1) (term-sort t2) *current-sort-order*)
    (return-from term-lex-order-vars :less))
  (when (sort< (term-sort t2) (term-sort t1) *current-sort-order*)
    (return-from term-lex-order-vars :greater))
  ;; same sort
  (if (term-is-variable? t1)
      (if (term-is-variable? t2)
	  (if (variable-eq t1 t2)
	      :same
	    ;; NOTE*!! 
	    (let ((vn1 (variable-name t1))
		  (vn2 (variable-name t2)))
	      (if (< vn2 vn1)
		  :greater
		:less)))
	:less)
    (if (term-is-variable? t2)
	:greater
      (if (term-is-application-form? t1)
	  (if (term-is-application-form? t2)
	      (if (method-is-of-same-operator (term-head t1)
					      (term-head t2))
		  ;; same op
		  (let ((ret-code :same))
		    (do ((t1-sub (term-subterms t1) (cdr t1-sub))
			 (t2-sub (term-subterms t2) (cdr t2-sub)))
			((or (null t1-sub)
			     (not (eq ret-code :same)))
			 ret-code)
		      (setq ret-code
			(term-lex-order-vars (car t1-sub) (car t2-sub)))
		      ))
		;; different op
		(op-lex-precedence (term-head t1) (term-head t2)))
	    :greater)
	:less))))


;;; LEX-CHECK : t1 t2 -> Bool
;;;
(defun lex-check (term1 term2)
  (declare (type term term1 term2)
	   (inline term-lex-order-vars)
	   (inline term-lex-order)
	   (values symbol))
  (if (pn-flag lex-order-vars)
      (term-lex-order-vars term1 term2)
    (term-lex-order term1 term2)))

;;; ORDER-EQUALITIES : CLAUSE -> CLAUSE'
;;; for each equality literal (po or neg), flip args if the
;;; right side is heavier. after possible flip, if the left
;;; side is heavier, set the `oriented-eq-bit' in the atom.
;;; if the atom is flipped, set scratch bit
;;;
(defun order-literal (lit input?)
  (declare (type boolean input?))
  (let* ((eq (literal-atom lit))
	 (alpha (term-arg-1 eq))
	 (beta (term-arg-2 eq)))
    (declare (type term eq alpha beta))
    (and (not (term-is-identical alpha beta))
	 (let ((alpha-bigger nil)
	       (beta-bigger nil))
	   (declare (type boolean alpha-bigger beta-bigger))
	   #||
	   (if (and (pn-flag symbol-elim)
		    (sym-elim alpha beta))
	       (setq alpha-bigger t)
	     (if (and (pn-flag symbol-elim)
		      (sym-elim beta alpha))
		 (setq beta-bigger t)
	       (if (term-occurs-in beta alpha)
		   (setq alpha-bigger t)
		 (if (term-occurs-in alpha beta)
		     (setq beta-bigger t)
		   (let ((rc (weight-lex-order alpha beta)))
		     (if (eq rc :greater)
			 (setq alpha-bigger t)
		       (if (eq rc :less)
			   (setq beta-bigger t))))))))
	   ||#
	   (if (or input? (term-occurs-in beta alpha))
	       (setq alpha-bigger t)
	     (if (term-occurs-in alpha beta)
		 (setq beta-bigger t)
	       (let ((rc (weight-lex-order alpha beta)))
		 (if (eq rc :greater)
		     (setq alpha-bigger t)
		   (if (eq rc :less)
		       (setq beta-bigger t))))))
	   ;;
	   (when (or alpha-bigger beta-bigger)
	     (when beta-bigger
	       (let ((new-atom
		      (make-term-with-sort-check *fopl-eq*
						 (list beta alpha))))
		 (declare (type term new-atom))
		 (setf (literal-atom lit) new-atom)
		 (set-bit (literal-stat-bits lit)
			  scratch-bit)))
	     (set-bit (literal-stat-bits lit)
		      oriented-eq-bit))
	   ))))

(defun order-equalities (clause &optional input)
  (declare (type clause clause)
	   (type boolean input)
	   (inline order-literal))
  (dolist (lit (clause-literals clause))
    (when (eq-literal? lit)
      (order-literal lit input))))

;;; sym-elim : a b -> bool
;;; true if a is complex, all args of a are unique vars,
;;; functor of a doesn't occur in b, and subset(vars(b), vars(a)).
;;; (if true, a = b can be made into a symbol-eliminatig demodulator).
;;;
(defun sym-elim (alpha beta)
  (declare (type term alpha beta))
  (cond ((or (term-is-variable? alpha)
	     (term-is-builtin-constant? alpha)
	     (term-is-lisp-form? alpha))
	 (return-from sym-elim nil))
	(t (return-from sym-elim
	     (and (operator-occurs-in (term-head alpha)
				      beta)
		  (var-subset beta alpha))))))

;;; VAR-SUBSET : TERM1 TERM2 -> Bool
;;; t iff vars(t1) is a subset of vars(t2).
;;;
(defun var-subset (t1 t2)
  (declare (type term t1 t2)
	   (values boolean))
  (let ((v1 (term-variables t1))
	(v2 (term-variables t2)))
    (declare (type list v1 v2))
    (subsetp v1 v2)))

;;; TERM-IDENT-X-VARS : Term1 Term2 -> Bool
;;;
(defun term-ident-x-vars (t1 t2)
  (declare (type term t1 t2)
	   (values boolean))
  (or (term-eq t1 t2)
      (and (term-type-eq t1 t2)
	   (cond ((term-is-variable? t1) t)
		 ((term-is-application-form? t1)
		  (if (method-w= (term-head t1) (term-head t2))
		      (let ((subs1 (term-subterms t1))
			    (subs2 (term-subterms t2)))
			(loop
			  (when (null subs1) (return t))
			  (unless (term-ident-x-vars (car subs1)
						     (car subs2))
			    (return nil))
			  (setq subs1 (cdr subs1)
				subs2 (cdr subs2))))
		    nil))
		 ((term-is-builtin-constant? t1)
		  (term-builtin-equal t1 t2))
		 ((term-is-lisp-form? t1)
		  (and (term-is-lisp-form? t2)
		       (equal (lisp-form-original-form t1)
			      (lisp-form-original-form t2))))
		 (t nil)))))

;;; EOF

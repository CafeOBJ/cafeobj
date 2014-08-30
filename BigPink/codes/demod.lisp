;;;-*-Mode:LISP; Package: CHAOS; Base:10; Syntax:Common-lisp -*-
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
;;;
(in-package :chaos)
#|=============================================================================
			    System:Chaos
			  Module:BigPink
			   File:demod.lisp
=============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

(declaim (special .demod-target-clause.)
	 (type (or null clause) .demod-target-clause.))
(defvar .demod-target-clause. nil)

(declaim (special .demod-used-clauses.)
	 (type list .demod-used-clauses.))
(defvar .demod-used-clauses. nil)

(declaim (special .current-demod-clause.)
	 (type (or null clause) .current-demod-clause.))
(defvar .current-demod-clause. nil)

(declaim (special .demod-to-be-used.)
	 (type list .demod-to-be-used.))
(defvar .demod-to-be-used. nil)

;;; METHOD-DEMODULATORS : Method -> List[Demodulator]
;;;
(defmacro method-demodulators (meth &optional (demod-table '*demodulators*))
  `(the list (gethash ,meth ,demod-table)))

;;; RULE->DEMODULATOR : Rule -> Demodulator
;;; - translates CafeOBJ rewrite rule to demodulator.
;;; - conditional rules are not supported.
;;;

(defun rule-2-demod (rule &optional (order :normal))
  (declare (type axiom rule)
	   (type symbol order))
  (make-demod :axiom rule
	      :order order))

(defun rule->demodulator (rule &optional (psys nil))
  (declare (type axiom rule)
	   (ignore psys)
	   (values (or null demod)))
  (let ((cond (axiom-condition rule)))
    (declare (type term cond))
    (if (is-true? cond)
	(rule-2-demod rule :normal)
      ;; I don't know how to treat this
      nil
      )))

;;; CAFEOBJ-RULES->DEMODULATORS : Module -> Void
;;; - translate every rewrite rules of Module to Demodulators.
;;; - generated demodulators are kept in demodulator table of given module.
;;;
(defun cafeobj-rules->demodulators (module)
  (declare (type module module)
	   (values t))
  (with-in-module (module)
    (let ((opinfos (module-all-operators *current-module*))
	  (demod-table (psystem-demodulators (module-proof-system module))))
      (declare (type list opinfos)
	       (type hash-table demod-table))
      (dolist (opinfo opinfos)
	(dolist (meth (opinfo-methods opinfo))
	  (declare (type method meth))
	  (let ((rules (method-rules-with-different-top meth)))
	    (declare (type list rules))
	    (dolist (r rules)
	      (declare (type axiom r))
	      (let ((demod (rule->demodulator r)))
		(when demod
		  (push demod (method-demodulators meth demod-table)))))))
	))))

;;; DYNAMIC-DEMODULATOR : Clause -> {:normal, :order-dep, nil}
;;;  :normal    -- regular demodulator
;;;  :order-dep -- lex- lr lrop- dependent demodulator
;;;  nil        -- cannnot be a demodulator
;;;
(defun dynamic-demodulator (clause)
  (declare (type clause clause)
	   (values symbol))
  (let ((l (ith-literal clause 1)))
    (declare (type literal l))
    (if (positive-eq-literal? l)
	(let* ((atom (literal-atom l))
	       (lhs (term-arg-1 atom))
	       (rhs (term-arg-2 atom)))
	  (declare (type term atom lhs rhs))
	  (when (term-is-identical lhs rhs)
	    (return-from dynamic-demodulator nil))
	  (when (test-bit (literal-stat-bits l) oriented-eq-bit)
 	    (if (pn-flag lrpo)
		(return-from dynamic-demodulator :normal)
	      (when (var-subset rhs lhs)
		(if (pn-flag dynamic-demod-all)
		    (return-from dynamic-demodulator :normal)
		  ;; 
		  (let ((wt-lft (term-weight lhs))
			(wt-rgt (term-weight rhs)))
		    (declare (type fixnum wt-lft wt-rgt))
		    (if (and (< wt-rgt (pn-parameter dynamic-demod-rhs))
			     (>= (- wt-lft wt-rgt)
				 (pn-parameter dynamic-demod-depth)))
			(return-from dynamic-demodulator :normal)))
		  )
		)))
	  ;;
	  (unless (pn-flag dynamic-demod-lex-dep)
	    (return-from dynamic-demodulator nil))
	  ;;
	  (when (pn-flag lrpo)
	    (if (and (var-subset rhs lhs)
		     (not (term-is-identical lhs rhs)))
		(return-from dynamic-demodulator :order-dep)
	      (return-from dynamic-demodulator nil)))
	  ;;
	  (if (not (pn-flag dynamic-demod-all))
	      (return-from dynamic-demodulator nil)
	    (if (and (term-ident-x-vars lhs rhs)
		     (not (term-is-identical lhs rhs)))
		(return-from dynamic-demodulator :order-dep)
	      (return-from dynamic-demodulator nil))))
      ;;
      nil)
    ))

;;; NEW-DEMODULATOR : Clause DemodFlag
;;; - make an equality unit into a demodulator.
;;; - returns new demodulator.
;;;
(defun new-demodulator (clause &optional (demod-flag nil))
  (declare (type clause clause)
	   (type symbol demod-flag)
	   (values demod))
  (incf (pn-stat new-demods))
  (let* ((atom (literal-atom (ith-literal clause 1)))
	 (lhs (copy-term-reusing-variables (term-arg-1 atom)
					   (term-variables (term-arg-1 atom))))
	 (rhs (copy-term-reusing-variables (term-arg-2 atom)
					   (term-variables (term-arg-2 atom)))))
    (declare (type term atom lhs rhs))
    (let* ((ax (make-simple-axiom lhs
				  rhs
				  nil	; type
				  nil	; behavioural -> to do
				  ))
	   (demod nil))
      (declare (type axiom ax)
	       (type (or null demod) demod))
      ;; specialization should be considered: TODO
      (setq demod (make-demod :axiom ax :order demod-flag
			      :clause clause))
      ;; must consider `demod-flag' here, : TODO
      ;; or at rewriting time......
      (push demod (gethash (term-head lhs) *demodulators*))
      ;;
      (incf (pn-stat demodulators-size))
      ;;
      demod ))
  )

;;; ===================
;;; DEMODULATION ENGINE
;;; ===================

(declaim (special *current-cafeobj-rule*)
	 (type (or null axiom) *current-cafeobj-rule*))
(defvar *current-cafeobj-rule* nil)

(declaim (special *demod-is-back-demod*))

(defvar *demod-is-back-demod* nil)

(defun demod-replace-term (t1 t2)
  (declare (type term t1 t2))
  (when (<= (pn-parameter demod-limit) *rule-count*)
    (throw 'rule-failure :demod-limit))
  (incf *rule-count*)
  (incf (pn-stat rewrites))
  (when (pn-flag trace-demod)
    (with-output-simple-msg ()
      (if (= 1 *rule-count*)
	  (progn
	    (if *demod-is-back-demod*
		(format t "<~D> back demod: " *rule-count*)
	      (format t "<~D> demod: " *rule-count*))
	    (term-print $$term))
	(format t "<~D>" *rule-count*))
      (let ((*print-indent* (+ *print-indent* 4)))
	(print-next)
	(term-print t1)
	(print-next)
	(format t "-(~a)-> "
		(if (clause-p .current-demod-clause.)
		    (clause-id .current-demod-clause.)
		  :*))
	(term-print t2))
      ))
  ;;
  (term-replace t1 t2)
  ;;
  (when (pn-flag trace-demod)
    (with-output-simple-msg ()
      (princ "  ==> ")
      (term-print $$term))))

(defun apply-one-demodulator (demod term)
  (if (eq (demod-order demod) :builtin)
      (if (apply-one-rule (demod-axiom demod) term)
	  (progn (incf (pn-stat rewrites)) t)
	nil)
    (apply-one-demodulator* demod term)))

(defun apply-one-demodulator* (demod term &aux (rule (demod-axiom demod)))
  (declare (type demod demod)
	   (type axiom rule)
	   (type term term))
  (declare (inline demod-replace-term))

  ;; non-harmfull but nonsence.
  (when (term-eq (rule-lhs rule) term)
    (return-from apply-one-demodulator* nil))
  ;;
  (let* ((*self* term)
	 (*do-unify* nil)
	 (contr nil)
	 (ok t))
    (declare (type term *self*)
	     (type (or null term) contr))
    ;;
    (multiple-value-bind (subst no-match E-equal)
	(pn-match (rule-lhs rule) term nil t)
      (declare (type list subst)
	       (ignore e-equal))
      (incf $$matches)
      (when no-match (return-from apply-one-demodulator* nil))
      (unless (beh-context-ok? rule term)
	(return-from apply-one-demodulator* nil))
      
      ;; match success -------------------------------------
      (block try-rule
	(catch 'rule-failure
	  (setq contr (set-term-color
		       (substitution-image subst (rule-rhs rule))))
	  (when (eq (demod-order demod) :order-dep)
	    (if (pn-flag lrpo)
		(setq ok (lrpo-greater term contr))
	      (setq ok (eq :less (lex-check contr term)))))
	  (when ok
	    (demod-replace-term  term contr)
	    (return-from apply-one-demodulator* t))))
      nil)))

;;; APPLY-DEMODULATOR : rule term -> Bool
;;;-----------------------------------------------------------------------------
;;; Returns true iff the rule has been sucessfully apply. Note that in this case
;;; "term" is also modified. 
;;; The associative extensions are automatiquely generated and applied if needed.
;;;
(defun apply-demodulator (demod term &aux (rule (demod-axiom demod)))
  (declare (type demod demod)
	   (type axiom rule)
	   (type term term))
  (let ((is-applied nil)
	(.current-demod-clause. (demod-clause demod)))
    (declare (type (or symbol clause) .current-demod-clause.))
    ;; avoid self application, current implementation cannot handle
    ;; this situation...
    (when (eq .current-demod-clause.
	      .demod-target-clause.)
      (return-from apply-demodulator nil))
    ;;
    (tagbody
      ;; now this test is useless, just a memo for future
      ;; versions.
       (when (rule-is-rule rule)
	 (if *rewrite-exec-mode*
	     (go do-apply)
	     (return-from apply-demodulator nil)))
       ;; rule is equation
       (when (and (not *cexec-normalize*)
		  (term-is-applform? term)
		  (method-has-trans-rule (term-head term)))
	 (return-from apply-demodulator nil))
      ;;---- 
     do-apply
      ;;----
      ;;
      ;; first apply the given rule.
      (setq is-applied (apply-one-demodulator demod term))
      ;; apply AC extension if failed..
      ;; 
      )
    ;; return t iff the rule is applied.
    (when is-applied
      (let ((cid (if (clause-p .current-demod-clause.)
		     (clause-id .current-demod-clause.)
		   :eval)))
	(pushnew cid .demod-used-clauses.))
      )
    ;;
    is-applied))

#|| NOT USED, and NOT fully implemented
;;;
(defun demod-apply-A-extensions (rule term top)
  (declare (type axiom rule)
	   (type term term)
	   (type method top))
  ;; (declare (optimize (speed 3) (safety 0)))
  (let ((listext (!axiom-a-extensions rule))
	(a-ext nil)
	(is-applied nil))
    (declare (type list litext)
	     (type (or null axiom) a-ext))
    (when (null listext)
      ;; then need to pre-compute the extensions and store then
      (setq listext (compute-A-extensions rule top)))
    (when (setq a-ext (car listext))
      ;; the first extension exists
      (setq is-applied (apply-one-demodulator a-ext term)))
    (setq listext (cdr listext))
    (when (setq a-ext (car listext))
      ;; the second extension exists
      (setq is-applied (or (apply-one-demodulator a-ext term)
			   is-applied)))
    (setq listext (cdr listext))
    (when (setq a-ext (car listext))
      ;; the third extension exists
      (setq is-applied (or (apply-one-demodulator a-ext term)
			   is-applied)))
    ;;
    is-applied))

(defun demod-apply-AC-extension (rule term top)
  (declare (type axiom rule)
	   (type term term)
	   (type method top)
	   (values (or null t)))
  (let ((listext (!axiom-ac-extension rule))
	(is-applied nil))
    (when (null listext)
      ;; then need to pre-compute the extensions and store then
      (setq listext (compute-AC-extension rule top)))
    (when (car listext)
      ;; the extension exists
      (setq is-applied (apply-one-demodulator (car listext) term)))
    is-applied))

||#

;;; APPLY-DEMODULATORS : TERM STRATEGY -> BOOLEAN
;;;
(defun apply-demodulators (term strategy)
  (declare (type term term)
	   (type list strategy))
  (labels ((apply-dt-rules (demods)
	     (declare (type list demods))
	     (block the-end
	       (dolist (demod demods)
		 (declare (type demod demod))
		 (when (apply-demodulator demod term)
		   (return-from the-end t)))))
	   (apply-rules-internal ()
	     (let ((top (term-head term)))
	       (declare (type method top))
	       (update-lowest-parse term)
	       (if (not (eq top (term-head term)))
		   (demod-normalize-term term)
		 (if (apply-dt-rules (or .demod-to-be-used.
					 (method-demodulators top)))
		     (demod-normalize-term term)
		   (demod-reduce-term term (cdr strategy)))
		 ))))
    ;;
    (apply-rules-internal)
    ))

;;;
;;; DEMOD-REDUCE-TERM : term strategy -> boolean
;;;
(defun demod-reduce-term (term strategy)
  (declare (type term term)
	   (type list strategy))
  (let ((occ nil)
	(top (term-head term))
	;; (*cexec-target* nil)
	)
    (declare (type (or null fixnum) occ)
	     (type method top))
    (cond ((null strategy)
	   ;; no strat, or exhausted.
	   (unless (term-is-lowest-parsed? term)
	     (update-lowest-parse term)
	     (unless (method= (term-method term) top)
	       (return-from demod-reduce-term (demod-normalize-term term))))
 	   (mark-term-as-reduced term)
	   )
	  
	  ;; whole
	  ((= 0 (the fixnum (setf occ (car strategy))))
	   #||
	   (when (eq top *rwl-predicate*)
	     (setq *cexec-target* term))
	   ||#
	   (unless (term-is-reduced? term)
	     (apply-demodulators term strategy)))

	  ;; explicit lazy
	  ((< (the fixnum occ) 0)
	   (let ((d-arg (term-arg-n term (1- (abs occ)))))
 	     (unless (term-is-reduced? d-arg) (mark-term-as-on-demand d-arg))
	     (demod-reduce-term term (cdr strategy))))

	  ;; normal case, reduce specified subterm
	  #||
	  (t (if (method-is-associative top)
		 (let ((list-subterms (list-assoc-subterms term top))
		       (lowest-parsed t))
		   (declare (type list list-subterms))
		   (dolist (x list-subterms)
		     (unless (demod-normalize-term x)
		       (setf lowest-parsed nil)))
		   (unless lowest-parsed
		     (mark-term-as-not-lowest-parsed term))
		   (demod-reduce-term term (list 0)))
		 (progn
		   (unless (demod-normalize-term (term-arg-n term (1- occ)))
 		     (mark-term-as-not-lowest-parsed term))
		   (demod-reduce-term term (cdr strategy)))))
	  ||#
	  (t (unless (demod-normalize-term (term-arg-n term (1- occ)))
	       (mark-term-as-not-lowest-parsed term))
	     (demod-reduce-term term (cdr strategy)))
	  )))

;;;

#||
(defun demod-method-rewrite-strategy (meth)
  (let ((strat (method-rewrite-strategy meth)))
    (if strat
	(if (= 0 (car (last strat)))
	    strat
	  (append strat '(0)))
      (progn
	(dotimes (x (cdr (method-name meth)))
	  (push (1+ x) strat))
	(push 0 strat)
	(nreverse strat)))))
||#

(defvar .demod-strat. 
    #((0)
      (1 0)
      (1 2 0)
      (1 2 3 0)
      (1 2 3 4 0)
      (1 2 3 4 5 0)
      (1 2 3 4 5 6 0)
      (1 2 3 4 5 6 7 0)
      (1 2 3 4 5 6 7 8 0)
      (1 2 3 4 5 6 7 8 9 0)
      (1 2 3 4 5 6 7 8 9 10 0) 
      ))

(defun demod-method-rewrite-strategy (meth)
  (let ((strat nil)
	(num-args (cdr (method-name meth))))
    (declare (type fixnum num-args)
	     (type list strat))
    (if (<= num-args 10)
	(aref .demod-strat. num-args)
      (progn
	(dotimes (x num-args)
	  (push (1+ x) strat))
	(push 0 strat)
	(nreverse strat)))))

(defun demod-normalize-term (term)
  (declare (type term term))
  (let ((strategy nil))
    (declare (type list strategy))
    (cond ((term-is-reduced? term)
	   (when (term-is-builtin-constant? term)
	     (update-lowest-parse term))
	   t)
	  ((null (setq strategy
		   (demod-method-rewrite-strategy (term-head term))))
	   (mark-term-as-reduced term)
	   t)
	  ;;
	  (t (demod-reduce-term term strategy)
	     nil))))

(defun clean-reduced-flag (term)
  (declare (type term term)
	   (values t))
  (when (or (term-is-builtin-constant? term)
	    (term-is-variable? term))
    (return-from clean-reduced-flag nil))
  (mark-term-as-not-reduced term)
  (when (term-is-application-form? term)
    (dolist (sub (term-subterms term))
      (clean-reduced-flag sub))))

(defun demod-rewrite (term &optional (module *current-module*))
  (declare (type term term)
	   (type module module)
	   (values term))
  ;; case of back demodulation
  (when .demod-to-be-used.
    (clean-reduced-flag term))
  ;;
  (with-in-module (module)
    (let ((*beh-rewrite* (and (not *rewrite-semantic-reduce*)
			      (module-has-behavioural-axioms module))))
      (declare (special *beh-rewrite*))
      (set-term-color-top term)
      (demod-normalize-term term)))
  term)

;;; 
;;; DEMODULATE-CLAUSE : CLAUSE -> Void
;;;
(defun demodulate-clause (clause)
  (declare (type clause clause))
  (let ((.demod-target-clause. clause)
	(.demod-used-clauses. nil)
	(.current-demod-clause. nil)
	(rwc (pn-stat rewrites)))
    (declare (type clause .demod-target-clause.)
	     (type fixnum rwc))
    (setq *term-memo-hash-hit* 0)
    (let ((*current-cafeobj-rule* (clause-axiom clause)))
      (dolist (lit (clause-literals clause))
	(declare (type literal lit))
	(demod-atom (literal-atom lit))))
    (unless (= (pn-stat rewrites) rwc)
      ;; there happened some rewrites
      (dolist (lit (clause-literals clause))
	(mark-literal lit))
      (setf (clause-parents clause)
	(nconc (clause-parents clause)
	       (list (cons :demod-rule (nreverse .demod-used-clauses.)))))
      )))

(defun demod-atom (atom)
  (setq *rule-count* 0)
  (setq $$matches 0)
  (setq $$term atom)
  #||
  (if (sort<= (term-sort atom) *fopl-sentence-sort* *current-sort-order*)
      (dolist (sub (term-subterms atom))
	(if (not (term-is-variable? sub))
	    (demod-atom sub)))
    (demod-rewrite atom))
  ||#
  (demod-rewrite atom)
  )

;;;
;;; APPLY-DEMOD-TO-CLAUSE : Demodulator Clause
;;;
(defun apply-demod-to-clause (demod clause)
  (let ((.demod-to-be-used. (list demod)))
    (declare (type list .demod-to-be-used.))
    (let ((.demod-target-clause. clause)
	  (.demod-used-clauses. nil)
	  (.current-demod-clause. nil)
	  (rwc (pn-stat rewrites)))
      (declare (type fixnum rwc))
      (setq *term-memo-hash-hit* 0)
      (let ((*current-cafeobj-rule* (clause-axiom clause)))
	(dolist (lit (clause-literals clause))
	  (declare (type literal lit))
	  (demod-atom (literal-atom lit))))
      (unless (= rwc (pn-stat rewrites))
	;; there happened some rewrites
	(dolist (lit (clause-literals clause))
	  (mark-literal lit))
	(return-from apply-demod-to-clause clause))
      nil)))

;;;
;;; BACK-DEMODULATE
;;;
(defun back-demodulate (demod-list clause input list-marker)
  (declare (type list demod-list)
	   (type clause clause)
	   (type symbol list-marker))
  (let ((demod (cdr (assq clause demod-list)))
	(*demod-is-back-demod* t))
    (declare (type (or null demod) demod))
    (when demod
      (let ((cls (get-clashable-clauses-from-atom
		  *full-lit-table*
		  (demod-lhs demod))))
	(declare (type list cls))
	(dolist (cl cls)
	  (declare (type clause cl))
	  (when (apply-demod-to-clause demod cl)
	    (incf (pn-stat cl-back-demod))
	    (unless (pn-flag quiet)
	      (when (or input (pn-flag print-back-demod))
		(with-output-simple-msg ()
		  (format t "* back demodulating ~d with ~d"
			  (clause-id cl)
			  (clause-id clause)))))
	    (clause-full-un-index-slow cl)
	    (setf (clause-container cl) nil) ; **
	    (setf (clause-parents cl)
	      (nconc (clause-parents cl)
		     (list (list :back-demod-rule (clause-id clause)))))
	    ;; (pre-process cl input list-marker)
	    (let ((new-cl (copy-clause cl)))
	      (declare (type clause new-cl))
	      (setf (clause-parents new-cl)
		(list (cons :back-demod-rule
			    (list (clause-id clause) (clause-id cl)))))
	      (pre-process new-cl input list-marker)
	      )
	    ))
	))
    ))

#|
(defun back-demodulate (demod-list clause input list-marker)
  (declare (type list demod-list)
	   (type clause clause)
	   (type symbol list-marker))
  (let ((demod (cdr (assq clause demod-list)))
	(*demod-is-back-demod* t))
    (declare (type (or null demod) demod))
    (when demod
      (let ((cls (get-clashable-clauses-from-atom
		  *full-lit-table*
		  (demod-lhs demod))))
	(declare (type list cls))
	(dolist (cl cls)
	  (declare (type clause cl))
	  (let ((new-cl (copy-clause cl)))
	    (declare (type clause new-cl))
	    (when (apply-demod-to-clause demod new-cl)
	      (incf (pn-stat cl-back-demod))
	      (unless (pn-flag quiet)
		(when (or input (pn-flag print-back-demod))
		  (with-output-simple-msg ()
		    (format t "* back demodulating ~d with ~d"
			    (clause-id cl)
			    (clause-id clause)))))
	      (clause-full-un-index-slow cl)
	      (setf (clause-container cl) nil) ; **
	      (setf (clause-parents new-cl)
		(list (cons :back-demod-rule
			    (list (clause-id clause) (clause-id cl)))))
	      (pre-process new-cl input list-marker)
	      )
	    ))
	))
    ))
|#

;;; LITERAL-TRUE-FALSE-REDUCE
;;; delete any false literals false or ~true
;;; nil : clause evaluated successfully
;;; t   : clause evaluated successfully to true
;;;       (clause/literals not deallocated)
;;;

(defmacro pn-is-true? (atom)
  (once-only (atom)
	     `(or (and (term-is-application-form? ,atom)
		       (is-true? ,atom))
		  (and (term-is-variable? ,atom)
		       (sort= (term-sort ,atom) *bool-sort*)))))

(defmacro safe-is-true? (term)
  (once-only (term)
	     `(and (term-is-applform? ,term)
		   (is-true? ,term))))

(defmacro safe-is-false? (term)
  (once-only (term)
	     `(and (term-is-applform? ,term)
		   (is-false? ,term))))

(defun pn-is-false? (lit)
  (declare (type literal lit))
  (let ((atom (literal-atom lit)))
    (declare (type term atom))
    #||
    (with-output-simple-msg ()
      (format t "pn-is-false?: ")
      (pr-literal lit *standard-output*)
      (print-next)
      (format t "type = ~s" (literal-type lit)))
    ||#
    (and (term-is-application-form? atom)
	 (or (is-false? atom)
	     (and (eq-literal? lit)
		  (let ((a1 (term-arg-1 atom))
			(a2 (term-arg-2 atom)))
		    (or (and (term-is-builtin-constant? a1)
			     (term-is-builtin-constant? a2)
			     (not (term-builtin-equal a1 a2)))
			(and (safe-is-true? a1) (safe-is-false? a2))
			(and (safe-is-false? a1) (safe-is-true? a2))))))))
  )

(defun literal-true-false-reduce (clause)
  (declare (type clause clause))
  (let ((literals nil)
	(delete? nil))
    (declare (type list literals))
    (dolist (lit (clause-literals clause))
      (declare (type literal lit))
      (let ((atom (literal-atom lit))
	    (true? nil)
	    (false? nil))
	(declare (type term atom))
	(setq true? (pn-is-true? atom))
	(setq false? (pn-is-false? lit))
	;;
	(if (or true? false?)
	    (if (or (and true?
			 (positive-literal? lit))
		    (and false?
			 (negative-literal? lit)))
		;; literal is true, so clause is true.
		(return-from literal-true-false-reduce t)
	      (if (or (and false?
			   (positive-literal? lit))
		      (and true?
			   (negative-literal? lit)))
		  ;; literal is false, so delete it
		  (setq delete? t)
		;; else store it as is
		(push lit literals)))
	  (push lit literals))))
    ;; done 
    (when delete?
      (setf (clause-literals clause) (nreverse literals))
      )
    ;;
    nil))

;;; SETUP-BUILTIN-DEMODULATORS
(defun setup-builtin-demodulators (mod)
  (with-in-module (mod)
    (let ((opinfos (module-all-operators mod)))
      (dolist (opinfo opinfos)
	(dolist (m (opinfo-methods opinfo))
	  (when (method-is-meta-demod m)
	    (let ((rules (method-all-rules m)))
	      (dolist (rule rules)
		(let ((demod (make-demod :axiom rule
					 :order :builtin
					 :clause :builtin)))
		  (push demod (gethash (term-head (rule-lhs rule))
				       *demodulators*)))))))))))

;;; SETUP-DEMODULATORS

(defun setup-demodulators ()
  (setup-builtin-demodulators *current-module*)
  (dolist (demod (psystem-demods *current-psys*))
    (new-demodulator demod :normal)))

;;; EOF

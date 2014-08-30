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
			  File:modconv.lisp
=============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; -----------------------------------------------
;;; CONVERTERS : CafeOBJ Axioms --> Fopl Sentences
;;; -----------------------------------------------

;;; MAKE-PIGNOSE-AXIOM
;;;
(defun make-pignose-axiom (lhs &key behavioural (type :pignose-axiom) label)
  (make-rule :lhs lhs
	     :rhs *bool-true*
	     :condition *bool-true*
	     :labels label
	     :behavioural behavioural
	     :type type)
  )

;;; AXIOM->FORMULA : Axiom -> FoplSentence
;;; convert CafeoBJ axiom (eq, ceq, beq, and cbeq) to FoplSentence
;;;
(declaim (special *elim-tf-in-axioms*))
(defvar *elim-tf-in-axioms* t)

(defun pn-set-tf-flag (value)
  (declare (ignore value))
  (if (pn-flag meta-paramod)
      (setq *elim-tf-in-axioms* nil)
    (setq *elim-tf-in-axioms* t)))

(defun pn-method-is-of-same-operator (m1 m2)
  (declare (type method m1 m2))
  (eq (method-operator m1)
      (method-operator m2)))

#||
(eval-when (:execute :load-toplevel)
  (setq .pn-ignore-ops.
    (list *bool-and*			; _and_
	  *bool-or*			; _or_
	  *bool-not*			; not_
	  *sort-membership*		; _:<SortId>
	  *bool-if*			; if_then_else_fi
	  *bool-imply*			; _implies_
	  *bool-iff*                    ; _iff_
	  *bool-xor*			; _xor_
	  *bool-equal*			; _==_
	  *beh-equal*			; _=b=_
	  *bool-nonequal*		; _=/=_
	  *beh-eq-pred*			; _=*=_
	  *bool-and-also*		; _and-also_
	  *bool-or-else*)))		; _or-else_
||#

(defun axiom->formula (ax)
  (declare (type axiom ax))
  (when *debug-formula*
    (format t "~&>> start axiom->formula conversion <<")
    (print-next)
    (print-chaos-object ax))
  ;; we ignore axioms of built-in Boolean operations
  ;; and, or, not, xor, ==, =/=, =b=, =*=, etc. user should be noticed.
  (let* ((lhs (axiom-lhs ax))
	 (head (if (term-is-applform? lhs)
		   (term-head (axiom-lhs ax))
		 nil))
	 (type (axiom-type ax)))
    (declare (type (or null method) head)
	     (type symbol type))
    (when (and head
	       (member head .pn-ignore-ops.
		       :test #'pn-method-is-of-same-operator))
      (when *chaos-verbose*
	(with-output-chaos-warning ()
	  (format t "~&axiom to formula translation: ignoring axiom")
	  (print-next)
	  (print-chaos-object ax)))
      (return-from axiom->formula nil))
    ;;
    (case type
      ((:equation :pignose-axiom :pignose-goal)
       #|| too early !!!
       (when (eq type :pignose-goal)
	 ;; we negate it before taking univeraly quantified closure:
	 (setq lhs (copy-term-reusing-variables lhs
						(term-variables lhs)))
	 (setq lhs
	   (make-term-with-sort-check *fopl-neg*
				      (list lhs))))
       ||#
       (let ((frm-lhs (cafeobj-term->formula lhs))
	     (frm-rhs (if (eq type :equation)
			  (cafeobj-term->formula (axiom-rhs ax))))
	     (frm-cond (if (eq type :equation)
			   (if (term-is-similar? *bool-true*
						 (axiom-condition ax))
			       nil
			     (cafeobj-term->formula (axiom-condition ax)))))
	     (frm nil)
	     (*elim-tf-in-axioms*
	      (if (not (eq (axiom-type ax) :equation))
		  t
		*elim-tf-in-axioms*)))
	 (declare (type (or null term)
			frm-lhs frm-rhs frm-cond frm))
	 ;;
	 (when *elim-tf-in-axioms*
	   (when (term-is-similar? *bool-true* frm-lhs)
	     (setq frm-lhs nil))
	   (when (term-is-similar? *bool-true* frm-rhs)
	     (setq frm-rhs nil))
	   (when (term-is-similar? *bool-false* frm-lhs)
	     (setq frm-lhs nil)
	     (setq frm-rhs (make-term-with-sort-check
			    *fopl-neg*
			    (list frm-rhs))))
	   (when (term-is-similar? *bool-false* frm-rhs)
	     (setq frm-rhs nil)
	     (setq frm-lhs (make-term-with-sort-check
			    *fopl-neg*
			    (list frm-lhs))))
	   (unless frm-lhs
	     (setq frm-lhs frm-rhs)
	     (setq frm-rhs nil)))
	 ;;
	 (if (and frm-lhs frm-rhs)
	     (if frm-cond
		 ;; ~cond | lhs = rhs (cond -> lhs = rhs)
		 (setq frm (make-term-with-sort-check
			    *fopl-or*
			    (list (make-term-with-sort-check
				   *fopl-neg*
				   (list frm-cond))
				  (make-term-with-sort-check
				   (if (and *fopl-two-equalities*
					    (axiom-is-behavioural ax))
				       *fopl-beq*
				     *fopl-eq*)
				   (list frm-lhs frm-rhs)))))
	       ;; lhs = rhs
	       (setq frm (make-term-with-sort-check
			  (if (and *fopl-two-equalities*
				   (axiom-is-behavioural ax))
			      *fopl-beq*
			    *fopl-eq*)
			  (list frm-lhs frm-rhs))))
	   ;;
	   (if frm-cond
	       ;; ~cond | lhs
	       (setq frm (make-term-with-sort-check
			  *fopl-or*
			  (list (make-term-with-sort-check
				 *fopl-neg*
				 (list frm-cond))
				frm-lhs)))
	     ;; lhs
	     (setq frm frm-lhs))
	   )
	 ;;
	 (when *debug-formula*
	   (format t "~%>> done <<")
	   (print-next)
	   (term-print frm))
	   
	 ;; if the axioms is :pignose-goal, i.e. declared by
	 ;; `goal', negate it. 

	 (when (eq type :pignose-goal)
	   (setq frm (copy-term-reusing-variables frm
						  (term-variables frm)))
	   (normalize-quantifiers frm)
	   (setq frm (make-term-with-sort-check *fopl-neg*
						(list frm))))
	 
	 ;;
	 frm))
      (otherwise
       (with-output-chaos-error ()
	 (format t "sorry, but transitions are not supported yet.")
	 (print-next)
	 (print-chaos-object ax)))
      )))

;;; MODULE-AXIOMS->CLAUSE : Module -> List[Clause]
;;;
(defun module-all-equations (mod)
  (declare (type module mod)
	   (values list))
  (let ((*seen* nil))
    (declare (special *seen*)
	     (type list *seen*))
    (labels ((all-own-equations (mod)
	       (declare (type module mod))
	       (reverse (module-equations mod)))
	     (imported-equations (mod)
	       (declare (type module mod))
	       (let ((res nil)
		     (subs (nreverse (module-direct-submodules mod))))
		 (declare (type list res subs))
		 (dolist (sub subs)
		   (block next-sub
		     (let ((sm (car sub)))
		       (declare (type module sm))
		       (when (memq sm *seen*)
			 (return-from next-sub nil))
		       (push sm *seen*)
		       (when (eq :using (cdr sub))
			 (return-from next-sub nil))
		       (let ((sub-ax nil)
			     (to-be-fixed (module-axioms-to-be-fixed mod)))
			 (dolist (ax (all-own-equations sm))
			   (push (or (cdr (assq ax to-be-fixed))
				     ax)
				 sub-ax))
			 (setq res
			   (nconc res
				  (nconc (nreverse sub-ax)
					 (mapcar #'(lambda (x)
						     (or (cdr (assq x to-be-fixed))
							 x))
						 (imported-equations sm)))
				  ))))))
		 ;;
		 (delete-duplicates res :test #'eq))))
      ;;
      (setq *seen* nil)
      (nconc (all-own-equations mod)
	     (imported-equations mod))
      )))

;;; MODULE-INCLUDES-FORMULA : Module -> Bool
;;; t iff module imports (semi)built-in FOPL module.
;;;
(defun module-includes-formula (mod)
  (declare (type module mod))
  (assq *fopl-sentence-module* (module-all-submodules mod)))

;;; MAKE-PN-APPL (mod method)
;;;
(defun make-pn-appl-pat (mod method)
  (with-in-module (mod)
    (make-term-with-sort-check
     method
     (mapcar #'(lambda (x)
		 (pn-make-var-on-the-fly x))
	     (method-arity method)))))

;;; COVER-SET-OF-SORT
;;;
(defun cover-set-of-sort (mod sort)
  (declare (type module mod)
	   (type sort* sort)
	   (values list))
  (let ((constructors (sort-constructors sort))
	(res nil))
    (declare (type list constructors res))
    (dolist (constr constructors)
      (push (make-pn-appl-pat mod constr) res))
    res))

;;; MODULE-COVER-SETS : mod -> list ( < sort . cover-set >) ...)
;;;
(defun module-cover-sets (mod &optional (no-built-in t))
  (declare (type module mod)
	   (values list))
  (let ((res nil))
    (dolist (sort (module-all-sorts mod))
      (declare (type sort* sort))
      (block next
	(when (and no-built-in
		   (let ((smod (sort-module sort)))
		     (or (module-is-hard-wired smod)
			 (module-is-system-module smod))))
	  (return-from next nil))
	(let ((cset (cover-set-of-sort mod sort)))
	  (when cset
	    (push (cons sort cset) res))))
      )
    res))

(defun get-all-methods-of-sort-strict (sort module)
  (declare (type sort* sort)
	   (type module module))
  (let ((res nil))
    (declare (type list res))
    (dolist (info (module-all-operators module))
      (dolist (m (opinfo-methods info))
	(unless (or (eq *void-method* m)
		    (is-skolem m module))
	  (when (sort= (method-coarity m) sort)
	    (push m res)))))
    res))

;;; INTRO-EXISTS : formula ex-vars -> formula
;;;
(defun intro-exists (form vars)
  (declare (type term form)
	   (type list vars))
  (if (null vars)
      form
    (let ((var-decl nil))
      (declare (type (or null term)))
      (if (cdr vars)
	  (setq var-decl
	    (make-right-assoc-normal-form *var-decl-list*
					  vars))
	(setq var-decl (car vars)))
      (make-term-with-sort-check *fopl-exists*
				 (list var-decl form)))))

;;; PN-NO-JUNK
;;; genarates axioms of no-junk.
;;; 
(defun pn-no-junk (mod)
  (declare (type module mod))
  #+:chaos-debug
  (declare (notinline op-lex-compare))
  (let ((csets (module-cover-sets mod))
	(all-axioms nil))
    (declare (type list csets))
    (with-in-module (mod)
      (dolist (cset csets)
	(declare (type list cset))
	(block next
	  (let* ((sort (car cset))
		 (covers (cdr cset))
		 (axioms nil))
	    (declare (type sort* sort)
		     (type list covers axioms))
	    (let ((constrs (sort-constructors sort))
		  (methods (get-all-methods-of-sort-strict sort mod))
		  (gen-methods nil))
	      (declare (type list constrs methods gen-methods))
	      ;;
	      #|
	      (dolist (const constrs)
		(when (method-arity const) (return-from next nil)))
		|#
	      ;;
	      (dolist (method methods)
		(unless (memq method constrs)
		  (let* ((arg-1 (make-pn-appl-pat mod method))
			 (vars (term-variables arg-1))
			 (pat nil)
			 (axiom-lhs nil))
		    (declare (type term arg-1)
			     (list vars pat)
			     (type (or null term) axiom-lhs))
		    (dolist (cover covers)
		      (let* ((real-cover (term-unique-vars cover))
			     (cover-vars (term-variables real-cover))
			     (eq-pat (make-term-with-sort-check
				      *fopl-eq*
				      (list
				       (copy-term-reusing-variables arg-1 vars)
				       real-cover))))
			(if (null cover-vars)
			    (push eq-pat pat)
			  ;; cover pat contains vars.
			  ;; introduce existential quantifier.
			  (push (intro-exists eq-pat cover-vars) pat))))
		    
		    (if (cdr pat)	; more than one pat
			(setq axiom-lhs
			  (make-right-assoc-normal-form *fopl-or*
							pat))
		      (setq axiom-lhs (car pat)))
		    ;;
		    (push (make-pignose-axiom axiom-lhs :label 'no-junk)
			  axioms)
		    (push method gen-methods)))
		
		)			; done for all methods for a sort
	      ;; redunduncy check. this is important
	      ;; if there are some axioms of the form
	      ;;    foo(X) = bar(X)
	      ;; and 
	      ;;    foo > bar
	      ;; foo from axioms.
	      (let ((do-delete nil))
		(declare (type list do-delete))
		(dolist (ax axioms)
		  (let* ((lhs (axiom-lhs ax))
			 (type (fopl-sentence-type lhs))
			 (lhs-meth nil)
			 (rules nil))
		    ;; lhs ::= 
		    ;;      |  meth(x) = constr1 ...
		    ;;      | \E[...] X = Y ...
		    (when (eq type :or)
		      (setq lhs (term-arg-1 lhs))
		      (setq type (fopl-sentence-type lhs)))
		    (case type
		      (:eq (setq lhs (term-arg-1 lhs))
			   (setq lhs-meth (term-head lhs)))
		      (:exists (setq lhs (term-arg-1 (term-arg-2 lhs)))
			       (setq lhs-meth (term-head lhs)))
		      (otherwise
		       (with-output-panic-message ()
			 (format t "pn-no-junk: illegal type ~s" type)))
		      )
		    (when lhs-meth
		      (setq rules (method-rules-with-different-top lhs-meth)))
		    ;;
		    (dolist (rule rules)
		      (let* ((rhs (rule-rhs rule)))
			(when (and (term-is-application-form? rhs)
				   (let ((rhs-meth (term-head rhs)))
				     (and (memq rhs-meth gen-methods)
					  (eq :greater
					      (op-lex-compare lhs-meth
							      (term-head rhs))))
				     ))
			  ;;
			  (pushnew ax do-delete))))))
		(dolist (ax do-delete)
		  (setq axioms (delete ax axioms))))
	      #||
	      (unless axioms
		;; we make
		;;   var = consr1 | var = constr2 ...
		(let ((var (pn-make-var-on-the-fly sort))
		      (pat nil)
		      (axiom-lhs nil))
		  (declare (type term var))
		  (dolist (cover covers)
		    (push
		     (make-term-with-sort-check
		      *fopl-eq*
		      (list
		       var
		       (term-unique-vars cover)))
		     pat))
		  (if (cdr pat)		; more than one pat
		      (setq axiom-lhs
			(make-right-assoc-normal-form *fopl-or*
						      pat))
		    (setq axiom-lhs (car pat)))
		  ;;
		  (push (make-pignose-axiom axiom-lhs :label 'no-junk)
			axioms)))
	      ||#
	      )
	    ;;
	    (setq all-axioms (nconc all-axioms axioms))
	    )))				; done for a sort
      all-axioms
      )))
  
;;; PN-NO-CONFUSION
;;; generates axioms (clauses) of no-confusion.
;;;
(defun pn-no-confusion (mod)
  (declare (type module mod))
  (let ((csets (module-cover-sets mod))
	(axioms nil))
    (declare (type list csets axioms))
    (with-in-module (mod)
      (dolist (cset csets)
	(declare (type list cset))
	(let ((covers (cdr cset)))
	  (do ((pat-list covers (cdr pat-list)))
	      ((endp pat-list))
	    (dolist (pat2 (cdr pat-list))
	      #||
	      ;; ~(a = b)
	      (push (make-pignose-axiom 
		     (make-term-with-sort-check
		      *fopl-neg*
		      (list (make-term-with-sort-check
			     *fopl-eq*
			     (list (term-unique-vars (car pat-list))
				   (term-unique-vars pat2)))))
		     :label 'no-conf)
		    axioms)
	      ||#
	      ;; (a = b) = false
	      (push (make-pignose-axiom
		     (make-term-with-sort-check
		      *fopl-eq*
		      (list (make-term-with-sort-check
			     *fopl-eq*
			     (list (term-unique-vars (car pat-list))
				   (term-unique-vars pat2)))
			    *bool-false*))
		     :label 'no-conf)
		    axioms)
	      ))))
      axioms
      )))


;;; MODULE-AXIOMS->CLAUSE : Proof-sytem -> List[Clause]
;;;
(defun module-axioms->clause (psys &aux (mod (psystem-module psys)))
  (declare (type psystem psys)
	   (type module mod))
  (include-FOPL mod)
  (compile-module mod)
  (unless (module-includes-formula mod)
    (with-output-chaos-error ('formula-error)
      (princ "module does not import FOPL-CLAUSE module.")))
  ;;
  (flet ((clause-is-valid-for-resolution (clause)
	   (declare (type clause clause))
	   (if (unit-clause? clause)
	       (let ((lit (car (clause-literals clause))))
		 (declare (type literal lit))
		 (if (positive-eq-literal? lit)
		     (if (term-is-lisp-form? (term-arg-2 (literal-atom lit)))
			 nil
		       t)
		   t))
	     t)))
    (with-in-module (mod)
      (let ((axs (module-all-equations mod))
	    (ax-clauses nil)
	    (demods nil)
	    (bi-demods nil))
	(declare (type list axs ax-clauses demods))
	(dolist (ax axs)
	  (let ((cls nil)
		(bi-demod nil)
		(demod nil))
	    (declare (type list cls demod))
	    (let ((lhs (axiom-lhs ax)))
	      (when (or (not (term-is-applform? lhs))
			(not (method-is-meta-demod (term-head lhs))))
		(dolist (cl (formula->clause-1
			     (axiom->formula ax)
			     psys
			     ax))
		  (declare (type clause cl))
		  (if (clause-is-builtin-demod cl)
		      (push cl bi-demod)
		    (if (clause-axiom-declared-as-demodulator cl)
			(push cl demod)
		      (when (clause-is-valid-for-resolution cl)
			(push cl cls)))))))
	    (setq ax-clauses (nconc ax-clauses (nreverse cls)))
	    (setq demods (nconc demods (nreverse demod)))
	    (setq bi-demods (nconc bi-demods (nreverse bi-demod)))))
	(setf (psystem-axioms psys) ax-clauses)
	(setf (psystem-demods psys) demods)
	(setf (psystem-bi-demods psys) bi-demods))
      ;; no junk/ no confusion axioms if required
      (when (pn-flag no-junk)
	(let ((axs (pn-no-junk mod)))
	  (dolist (ax axs)
	    (dolist (cl (formula->clause-1
			 (axiom->formula ax)
			 psys
			 ax))
	      (declare (type clause cl))
	      (push cl (psystem-axioms psys))))))
      (when (pn-flag no-confusion)
	(let ((axs (pn-no-confusion mod)))
	  (dolist (ax axs)
	    (dolist (cl (formula->clause-1
			 (axiom->formula ax)
			 psys
			 ax))
	      (declare (type clause cl))
	      (push cl (psystem-axioms psys))))))
      )))

;;; EOF

;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
;;;
;;; Copyright (c) 2000-2015, Toshimi Sawada. All rights reserved.
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
#|=============================================================================
                                  System:CHAOS
                                 Module:e-match
                             File:match-system.lisp
Based on the implementation of OBJ3 system. 
=============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;;                        The Mach System
;;; (defvar *match-debug* nil)
;;;-----------------------------------------------------------------------------
;;; A match system is a system of oriented equations which first term may
;;; contains variables and the second one is a ground term
;;; This is used for solving matching modulo E of some equational theories.
;;;
;;; The match system consists of the following two types of sets of equations:
;;; (1) MATCH-ENVIRONMENT : {t1 = t2 ...} where
;;;     t1 is a variable, this is a list of bindings, i.e, the list of pair
;;;     (variable . value). 
;;; (2) SYSTEM-TO-SOLVE : {t1 = t2 ... } where t1 is not a variable.
;;;
;;; The matching process try to solve this match system,i.e, to make
;;; `system-to-solve' empty, resulting `match-environment' holds the \sigma
;;; substitution. 
;;;

#| Match Rules =================================================================

   The matching process is based on the following general rules
   which are adapted to OS case.

   (1) Decomposition.  

       f(t1,...,tn) == f(t1',...,tn')   
       ------------------------------     if f \in Fd
       {t1 == t1' & ... & tn == tn'}  

    (2) Conflict (symbol crash).

        f(t1,...,tn) == g(t1',...,tn')   
        ------------------------------     if f,g \in Fd
                      F

    (3) Trivial Equation. 

        t == t  &  U   
       -------------
             U      

   (4)  Mutation. 

        t1 == t2 & U
      ---------------------     if t1, t2 \in E (in some sense )
       MUT(E)(t1 == t2 & U)

   (5)  Coalesce.

        x:s == y:s' & U
       ------------------       if x,y \in Var(U) and s' <= s
       x == y &  U{x -> y} 

   (6)  Merge - there is a merge operation - which I have yet to properly formulate

==============================================================================|#

;;; First, we give definitions and operations of each of the above constructs
;;; in a bottom up manner, then define the match sytem and its friends.

;;; Equation ===================================================================
;;;
;;; An equation t1 == t2 is represented by a pair (t1 . t2) .

(defmacro make-equation (____t1 ____t2) `(cons ,____t1 ,____t2))
(defmacro equation-t1 (____eq) `(the term (car ,____eq)))
(defmacro equation-t2 (____eq) `(the term (cdr ,____eq)))

;;; MATCH-DECOMPOSE-EQUATION : term-1 term-2 -> 
;;;
;;; The equation 'equation' to be decomposed is supposed to be of the form
;;; t1 == t2 with t1 and t2 in standard form, i.e. in normal form for
;;; idempotence and zero (identity) if any.
;;;
;;;    (1) Decomposition.  
;;;
;;;       f(t1,...,tn) == f(t1',...,tn')   
;;;       ------------------------------     if f \in Fd
;;;       {t1 == t1' & ... & tn == tn'}  
;;;
;;;    (2) Conflict (crash of symbols).
;;;
;;;        f(t1,...,tn) == g(t1',...,tn')   
;;;        ------------------------------     if f,g \in Fd
;;;                      F
;;;

;;; we avoid `labels' because some Common Lisp implementation does not handle
;;; it well, espacialy for KCL and its family (AKCL, GCL...)
;;;

;;; GLOBL FLAG
(declaim (special *do-unify*))
;;; if t, matching routines perform unification instead of matching.
;;;
(defvar *do-unify* nil)
(declaim (special *one-way-match*))
(defvar *one-way-match* t)
(declaim (special *do-empty-match*))
(defvar *do-empty-match* nil)

;; #-GCL (declaim (inline !match-decompose-on-demand))

(defun !match-decompose-on-demand (t1 t2 result)
  (declare (type term t1 t2)
           (type list result)
           (values (or null t)))
  ;; perform on-demand reduction of t2, then try decompose.
  ;; returns t on failure.
  (if (term-is-on-demand? t2)
      ;; `normalize-term' may destructively rewrites t2,
      ;; returns T iff it did not perform rewriting.
      (progn
        (mark-term-as-not-on-demand t2)
        (if (normalize-term t2)
            t
          (!match-decompose t1 t2 result)))
    t)
  )

(defun occurs-in (v term)
  (cond ((term-is-variable? term)
         (variable-eq v term))
        ((term-is-application-form? term)
         (dolist (sub (term-subterms term))
           (when (occurs-in v sub)
             (return-from occurs-in t)))
         nil)
        (t nil)))


(defun !match-decompose (t1 t2 res)
  (if *do-unify*
      (!match-decompose-unify t1 t2 res)
    (!match-decompose-match t1 t2 res)))

(defun method-theory-info-for-matching! (meth)
  (if *do-empty-match*
      the-e-property
    (method-theory-info-for-matching meth)))

(defun !match-decompose-unify (t1 t2 res)
  (declare (type term t1 t2)
           (type list res)
           (values (or null t)))
  (cond ((term-is-variable? t1)
         ;; [1] t1 is variable
         ;; OS sort check.
         (when (variable-eq t1 t2)
           ;; trivial equation, discard.
           (return-from !match-decompose-unify nil))
         (when (occurs-in t1 t2)
           (return-from !match-decompose-unify t))
         ;;
         (if (sort<= (term-sort t2) (term-sort t1) *current-sort-order*)
             (let ((cval (variable-image (cdr res) t1)))
               (if cval 
                   (progn
                     (!match-decompose-unify cval t2 res))
                 (cond ((term-is-variable? t2)
                        (setq cval (variable-image (cdr res) t2))
                        (if (not cval)
                            (push (make-equation t1 t2) (cdr res))
                          (unless (variable-eq t1 cval)
                            (push (make-equation t1 t2) (cdr res))))
                        nil)
                       (t (push (make-equation t1 t2) (cdr res))
                          nil))
                 ))                     ; success
           ;; incomparable sorts
           t))                          ; fail

        ;; [2] t1 is not variable, t2 is variable.
        ((term-is-variable? t2)
         (!match-decompose-unify t2 t1 res))
    
        ;; [3] t1 or t2 is builtin constant.

        ((term-is-builtin-constant? t1)
         (not (term-builtin-equal t1 t2)))

        ;; [4] t1 & t2 is application form.
        (t (let* ((t1-top (term-head t1))
                  (t2-top (term-head t2))
                  (th-info (method-theory-info-for-matching! t1-top)))
             ;; since it is OS-matching, we only
             ;; test the equality of the operator.
             (if (method-is-of-same-operator+ t1-top t2-top)
                 ;; f(x, y, z ...) = f(x',y',z'...)
                 (if (theory-info-empty-for-matching th-info)
                     ;;
                     ;; the empty theory, do the full decompose.
                     ;;
                     (let ((t1-subterms (term-subterms t1))
                           (t2-subterms (term-subterms t2)))
                       (declare (type list t1-subterms t2-subterms))
                       (loop            ; for each subterm try decomposition.
                         (unless t1-subterms (return nil))
                         (let ((ng (!match-decompose-unify (car t1-subterms)
                                                           (car t2-subterms)
                                                           res)))
                           (when ng
                             (return-from !match-decompose-unify t)))
                         (setf t1-subterms (cdr t1-subterms)
                               t2-subterms (cdr t2-subterms)))
                       nil)
                   ;;
                   ;; if the theory has equational theory, we do not
                   ;; perform full decomposition.
                   ;;
                   (progn
                     (push (make-equation t1 t2) (cdr res))
                     nil))
               ;;
               ;; the different top level
               ;; possibly maches only when zero case...
               (if (or (test-theory .Z. (theory-info-code th-info))
                       (test-theory .Z. (theory-info-code
                                         (method-theory-info-for-matching!
                                          (term-head t2)))))
                   (progn (push (make-equation t1 t2) (cdr res))
                          nil)
                 ;; will never match
                 t))))))

(defun !match-decompose-match (t1 t2 res)
  (declare (type term t1 t2)
           (type list res)
           (values (or null t)))
  (with-match-debug ()
    (format t "~%** !match-decompose-match:")
    (print-next)
    (princ "-t1: ") (term-print-with-sort t1)
    (print-next)
    (princ "-t2: ") (term-print-with-sort t2))
  (cond
    ;; [1] t1 is variable
    ((term-is-variable? t1)
     ;; OS sort check.
     (if (sort<= (term-sort t2) (term-sort t1) *current-sort-order*)
         (progn 
           (push (make-equation t1 t2) (cdr res))
           nil)
       ;; try again after possible on-demand reduction of t2.
       (!match-decompose-on-demand t1 t2 res)))
    
    ;; [2] t1 is not variable, t2 is variable.
    ((term-is-variable? t2) 
     (if *one-way-match*
         (progn
           (with-match-debug ()
             (print-next)
             (princ ">> FAIL for t2 is variable."))
           t)                            ; fail
       (!match-decompose-match t2 t1 res)))
    
    ;; [3] t1 or t2 is builtin constant.
    ((term-is-builtin-constant? t1)
     (let ((ans (not (term-builtin-equal t1 t2))))
       (with-match-debug ()
         (print-next)
         (if ans
             (princ ">> SUCCESS, builtin-equal.")
           (princ ">> FAIL, builtin not equal.")))
       ans))

    ;; [4] t1 is an application form.
    (t (let* ((t1-top (term-head t1))
              (th-info (method-theory-info-for-matching! t1-top)))
         (if (term-is-builtin-constant? t2)
             (if (not (theory-info-empty-for-matching th-info))
                 (progn (push (make-equation t1 t2) (cdr res))
                        nil)
               (progn
                 (with-match-debug ()
                   (print-next)
                   (princ ">> FAIL, t2 is builtin."))
                 t))
           ;; t2 also is an application form.
           (let ((t2-top (term-head t2)))
             ;; since it is OS-matching, we only
             ;; test the equality of the operator.
             (if (method-is-of-same-operator+ t1-top t2-top)
                 ;; f(x, y, z ...) = f(x',y',z'...)
                 (if (theory-info-empty-for-matching th-info)
                     ;;
                     ;; the empty theory, do the full decompose.
                     ;;
                     (let ((t1-subterms (term-subterms t1))
                           (t2-subterms (term-subterms t2)))
                       (declare (type list t1-subterms t2-subterms))
                       (with-match-debug ()
                         (format t "~%>> empty theory: do the full decompose..."))
                       (loop            ; for each subterm try decomposition.
                         (unless t1-subterms (return nil))
                         (let ((ng (!match-decompose-match (car t1-subterms)
                                                           (car t2-subterms)
                                                           res)))
                           (when (and ng
                                      (!match-decompose-on-demand t1 t2 res))
                             (return-from !match-decompose-match t)))
                         (setf t1-subterms (cdr t1-subterms)
                               t2-subterms (cdr t2-subterms)))
                       nil)
                   ;;
                   ;; if the theory has equational theory, we do not
                   ;; perform full decomposition.
                   ;;
                   (progn
                     (with-match-debug ()
                       (format t "~%>> has theory: add their pair."))
                     (push (make-equation t1 t2) (cdr res))
                     nil))
           
               ;;
               ;; the different top level
               ;; possibly maches only when zero case or on-demand. 
               ;;
               (if (term-is-on-demand? t2)
                   (progn
                     (with-match-debug ()
                       (format t "~%>> term t2 is on demand."))
                     (mark-term-as-not-on-demand t2)
                     (if (normalize-term t2)
                         ;; no reduction has been performed.
                         (if (or (test-theory .Z. (theory-info-code th-info))
                                 (test-theory .Z. (theory-info-code
                                                   (method-theory-info-for-matching!
                                                    (term-head t2)))))
                             (progn (push (make-equation t1 t2) (cdr res))
                                    nil)
                           ;; will never match
                           t)
                       ;; t2 is rewritten
                       (!match-decompose t1 t2 res)))
                 ;; t2 is not on demand.
                 (if (or (test-theory .Z. (theory-info-code th-info))
                         (test-theory .Z. (theory-info-code
                                           (method-theory-info-for-matching!
                                            (term-head t2)))))
                     (progn 
                       (with-match-debug ()
                         (format t "~%>> theory Z."))
                       (push (make-equation t1 t2) (cdr res))
                       nil)
                   ;; will never match
                   t)) )))))))


(defun match-decompose-equation (t1 t2 &optional (sigma nil))
  (declare (type term t1 t2))
  (when sigma
    (setq sigma (copy-list sigma)))
  (let* ((list-of-decomposed-equation (cons nil sigma))
         (no-match (if *do-unify*
                       (!match-decompose-unify t1 t2 list-of-decomposed-equation)
                     (!match-decompose-match t1 t2 list-of-decomposed-equation))))
    (declare (type list list-of-decomposed-equation)
             (type (or null t) no-match))
    (cond (no-match (values (cdr list-of-decomposed-equation) t)) ; no match
          (t (if (cdr list-of-decomposed-equation)
                 (let ((new-subst
                        (normal-form-sub (cdr list-of-decomposed-equation) nil)))
                   (if new-subst
                       (values new-subst no-match)
                     ;; 
                     (values (cdr list-of-decomposed-equation) no-match)))
               (values nil nil))))))    ; equational equal
  
(defun normal-form-sub (sub ans)
  (if sub
      ;; occur check here
      (let* ((v1 (caar sub))
             (t1 (apply-subst ans (cdar sub)))
             (new-pair (make-equation v1 t1)))
        (if (occurs-in v1 t1)
            nil
          (normal-form-sub
           (cdr sub)
           (cons new-pair
                 (mapcar #'(lambda (x)
                             (make-equation
                              (apply-subst (list new-pair)
                                           (equation-t1 x))
                              (apply-subst (list new-pair)
                                           (equation-t2 x))))
                         ans)))))
    ans))

#||
(defun apply-subst (sigma term)
  (if sigma
      (cond ((term-is-variable? term)
             (let ((im (variable-image sigma term)))
               (if im                   ; i.e. im = sigma(term)
                   (values im t)
                 (values term nil))))
            ((term-is-builtin-constant? term) term)
            ((term-is-lisp-form? term) term)
            ((term-is-application-form? term)
             (let ((l-result nil)
                   (modif-sort nil))
               (dolist (s-t (term-subterms term))
                 (multiple-value-bind (image-s-t same-sort)
                     (apply-subst sigma s-t)
                   (unless same-sort
                     ;; (update-lowest-parse s-t)
                     (setq modif-sort t))
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
                         t))))
            (t (with-output-panic-message ()
                 (princ "apply-subst: encoutered illegual term")
                 (terpri)
                 (term-print term))))
    term))
||#

(defun apply-subst (sigma term)
  (cond ((term-is-variable? term)
         (let ((im (variable-image sigma term)))
           (if im                       ; i.e. im = sigma(term)
               (values im t)
             (values term nil))))
        ((term-is-builtin-constant? term) term)
        ((term-is-lisp-form? term) term)
        ((term-is-application-form? term)
         (let ((l-result nil)
               (modif-sort nil))
           (dolist (s-t (term-subterms term))
             (multiple-value-bind (image-s-t same-sort)
                 (apply-subst sigma s-t)
               (unless same-sort
                 ;; (update-lowest-parse s-t)
                 (setq modif-sort t))
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
                     t))))
        (t (with-output-panic-message ()
             (princ "apply-subst: encoutered illegual term")
             (print-next)
             (term-print-with-sort term))))
  )

;;; M-SYSTEM-TO-SOLVE ==========================================================
;;; A m-system-to-solve is a set of equation of the form t1==t2 where, t1 is not
;;; a variable. 
;;;
;;; Signature:
;;; -- Constructors  
;;; create-m-system : term term -> system
;;; new-m-system  : -> system (the empty system).
;;; make-m-system : list(equation) list(equation) -> system
;;; -- System Operators 
;;; add-m-system : system system -> system~
;;; add-equation-to-m-system : system equation -> system~
;;; m-system-to-list : system -> list[equation]
;;; size-of-m-system : system -> integer
;;; m-system-is-empty? : system -> bool
;;; m-system-extract-one : system -> system operator-theory

;;; Implementation:
;;; represented by a LIST treated by a set.

;;; assume t1 is not a variable.
(deftype msystem () 'list)
(defmacro create-m-system (?_t1 ?_t2) `(list (make-equation ,?_t1 ,?_t2)))

(defun print-m-system (m)
  (declare (type msystem m)
           (values t))
  (dolist (e m)
    (let ((t1 (equation-t1 e))
          (t2 (equation-t2 e)))
      (format t "~%[m-system]===========")
      (format t "~&t1 = ") (term-print-with-sort t1)
      (format t "~&t2 = ") (term-print-with-sort t2))))

;;; creates new empty m-system-to-solve.
(defmacro new-m-system () `(cons nil nil)) ; In order to be able to modify it

;;; adjoint to sys1 each equation of sys2 which is not already in sys1. 
;;; NOE: "sys1" is modified, "sys2" must not be modified
;;;       currently we do'nt check though ...
(defmacro add-m-system (?!_sys1 ?!_sys2) `(append ,?!_sys1 ,?!_sys2))

(defmacro m-system-is-empty? (??sys) `(null (car ,??sys)))

(defmacro m-system-to-list (??_sys)
  (once-only (??_sys)
    ` (if (m-system-is-empty? ,??_sys)
          (cdr ,??_sys)
          ,??_sys)))

(defmacro size-of-m-system (!_?sys)
  (once-only (!_?sys)
    ` (if (m-system-is-empty? ,!_?sys)
          (length (the list (cdr ,!_?sys)))
          (length ,!_?sys))))

;;; Add an equation to the system.
;;;
(defun add-equation-to-m-system (sys eq)
  (declare (type list sys)
           (type t eq)
           (values t))
  (unless (member eq sys :test #'eq)
    (if (m-system-is-empty? sys)
        (rplaca sys eq)                 ; remove the nil on top
        (rplacd sys (cons eq (cdr sys))))))

;;; Returns a system from two list of equations. One of the two lists should be
;;; non empty. Assumes each equation-t1 is not a variable.
;;;
(declaim (inline make-m-system))

(defun make-m-system (l1 l2)
  (declare (type list l1 l2)
           (values msystem))
  (if (null (car l1))
      (union (cdr l1) l2)
      (if (null (car l2))
          (union l1 (cdr l2))
          (union l1 l2))))

;;; Returns the biggest system extracted from "sys", which is homogenous with
;;; respect to the current theory.
;;; For example if * and + are AC then it may return a system whose equations
;;; have all + for top symbol of their left hand side. 

;;; Note that if + and * are only commutative then the notion of homogenous
;;; system can be extended to include system like {x+z == a+b, x*a == b*a}.
;;; So the notion of homogenous system depends on the theory. This is not
;;; implemented yet. 

;;; "sys" is supposed to be non empty and to contain equations of the 
;;; form t1==t2 which are all such that t1 is NOT a variable.

(defun m-system-extract-one-system (sys)
  (declare (type list sys)
           (values list theory-info))
  (let ((extracted-sys nil)
        (theory-is-empty nil)
        (disc-method nil))
    (dolist (eq (m-system-to-list sys))
      (let ((t1 (equation-t1 eq)))
        (declare (type term t1))
        (if (term-is-application-form? t1)
            (let ((t1-top (term-method t1)))
              (cond
                ;; t1-top has no specific theory for matching.
                ((theory-info-empty-for-matching
                  (method-theory-info-for-matching! t1-top))
                 (when disc-method
                   (unless (theory-info-empty-for-matching
                            (method-theory-info-for-matching! disc-method))
                     ;; The greatest priority is given to the empty theory.
                     ;; The extracted system is reset.
                     (setq disc-method t1-top)
                     (setq extracted-sys nil)))
                 (setq theory-is-empty t)
                 (push eq extracted-sys))
                
                ;; t1-top has non empty theory.
                (t (if disc-method
                       ;; Gather homogenous ones.
                       (when (method-is-of-same-operator+ disc-method t1-top)
                         (push eq extracted-sys))
                       (unless theory-is-empty
                         (setq disc-method t1-top)
                         (push eq extracted-sys))))))
            (progn
              (setq theory-is-empty t)
              (push eq extracted-sys)
              (setq disc-method nil)))))
    (values extracted-sys
            (if disc-method
                (method-theory-info-for-matching! disc-method)
              (theory-info *the-empty-theory*)))))

;;; MATCH ENVIRONMENT ==========================================================

;;; An environment is a particular kind of system the equation of
;;; which are of the form (x == t) where x is a variable and t a term-
;;;

;;; Signature:
;;; create-environment : Term Term -> Environment
;;; new-environment    : -> Environment (the empty environment).
;;; environment-to-list  : Environment -> List[Equation] .
;;; match-insert-if-coherent-with: 
;;;                Environment Environment System System -> Environment~,
;;;                                                         signals(no_coherent)
;;; add-equation-to-environment : Environment Equation -> Environment~
;;; environment-copy1: Environment -> Environment .
;;; environment-to-substitution: Environment -> Substitution
;;; environment-image: Environment Variable -> Term or nil

;;; Implementation:
;;; list of equation or (nil . list of equation)

(defmacro create-environment (???t1 ???t2) `(list (cons ,???t1 ,???t2)))

(defmacro new-environment () `(cons nil nil))

(defmacro environment-to-list (?_!env)
  (once-only (?_!env)
    `(if (null (car ,?_!env))
         (cdr ,?_!env)
       ,?_!env)))
   
(defun add-equation-to-environment (env eq)
  (if (null (car env))
      (rplaca env eq)
    (rplacd env (push eq (cdr env)))))

(defmacro environment-copy1 (___?env) `(copy-list ,___?env))

(defmacro environment-to-substitution (___?env) ___?env)

(defmacro environment-image (??_?env ??_?var)
  (once-only (??_?env ??_?var)
    `(if (null (car ,??_?env))
         (cdr (assoc ,??_?var (cdr ,??_?env) :test #'variable-eq))
       (cdr (assoc ,??_?var ,??_?env :test #'variable-eq)))))

;;;  { ... x == t ...} U { ... x == t' ...} 
;;;
;;; Insert the equation in "eq-list"  in the environment "new-env" iff they are
;;; of the form x == t and are not present in "test-env". If x == t' is present
;;; in "test-env" and t' =/= t then it signals no_coherent.
;;; Then all equations present in "test_env" are added to "new_env" "test_env"
;;; must not be modified. 
;;; U: used by "match-system.dec-merg" and "match-add-m-system"

(defun match-insert-if-coherent-with (new-env test-env new-sys eq-list &optional (check-match nil))
  ;; note that new-env and new-sys are both initialy of the form (nil.nil)
  (block the-end
    (with-match-debug ()
      (format T "~%insert:--------------------------------------")
      (print-next)
      (format t "new-env = ")
      (if (car new-env)
          (dolist (eq new-env)
            (print-next)
            (format t "~%  LHS = ") (term-print-with-sort (equation-t1 eq))
            (print-next)
            (format t "  RHS = ") (term-print-with-sort (equation-t2 eq))
        (princ "empty")))
      (print-next)
      (format t "test-env = ")
      (if (car test-env)
          (dolist (eq test-env)
            (format t "~%  LHS = ") (term-print-with-sort (equation-t1 eq))
            (print-next)
            (format t "  RHS = ") (term-print-with-sort (equation-t2 eq)))
        (princ "empty"))
      (terpri))
    (dolist (eq eq-list)
      (let ((t1 (equation-t1 eq))
            (t2 (equation-t2 eq)))
        (cond ((term-is-variable? t1)
               ;; checking of the sort information; redundant with
               ;; `decompose-equation'.
               (unless (sort<= (term-sort t2) (variable-sort t1)
                               *current-sort-order*)
                 (with-match-debug ()
                   (print-next)
                   (format t "-- non coherent, sort match fail."))
                 (return-from the-end t))
               ;; new-env may be  modified.
               (let ((image-of-t1 (variable-image test-env t1)))
                 (if image-of-t1
                     (unless (term-equational-equal image-of-t1 t2)
                       (with-match-debug ()
                         (format t "~%-- non coherent, var binding conflicts in env."))
                       (return-from the-end t)) ; i.e  no-coherent
                   (let ((image-of-t1-in-new (variable-image new-env t1)))
                     (if image-of-t1-in-new
                         (unless (term-equational-equal image-of-t1-in-new
                                                        t2)
                           (with-match-debug ()
                             (format t "~%-- non coherent, var binding in new-env."))
                           (return-from the-end t))
                       (add-equation-to-environment new-env eq))))))
              (check-match
               (when (term-is-variable? t2)
                 (with-match-debug ()
                   (format t "~%-- non coherent, t2 is variable."))
                 (return-from the-end t))
               (if (and (term-is-applform? t2)
                        (term-is-applform? t1))
                   (let ((t1-head (term-head t1))
                         (t2-head (term-head t2)))
                     (if (method-is-of-same-operator+ t1-head t2-head)
                         (add-equation-to-m-system new-sys eq)
                       (let ((match-info (method-theory-info-for-matching! t1-head)))
                         (if (test-theory .Z. (theory-info-code match-info))
                             (add-equation-to-m-system new-sys eq)
                           (progn
                             (with-match-debug ()
                               (format t "~%-- non coherent, func conflict."))
                             (return-from the-end t))))))
                 (add-equation-to-m-system new-sys eq)))
              ;;
              (t (add-equation-to-m-system new-sys eq)))))

    ;; add now all the equation of test-env into new-env (copy test-env)
    (cond ((null (car test-env)) ())
          ((null (car new-env))
           (let ((l (environment-copy1 test-env)))
             (rplaca new-env (car l))
             (rplacd new-env (cdr l))) )
          (t (nconc new-env test-env)))
    (with-match-debug ()
      (format t "~%insert: return -- coherent -------------------")
      
      )
    nil                                 ; i.e. the new-env is coherent
    ))

#||
(defun match-insert-if-coherent-with (new-env test-env new-sys eq-list &optional (check-match nil))
  ;; note that new-env and new-sys are both initialy of the form (nil.nil)
  (block the-end
    (dolist (eq eq-list)
      (let ((t1 (equation-t1 eq))
            (t2 (equation-t2 eq)))
        (cond ((term-is-variable? t1)
               ;; checking of the sort information; redundant with
               ;; `decompose-equation'.
               (unless (sort<= (term-sort t2) (variable-sort t1)
                               *current-sort-order*)
                 (return-from the-end t))
               ;; new-env may be  modified.
               (let ((image-of-t1 (variable-image test-env t1)))
                 (if image-of-t1
                     (unless (term-equational-equal image-of-t1 t2)
                       (return-from the-end t)) ; i.e  no-coherent
                   (let ((image-of-t1-in-new (variable-image new-env t1)))
                     (if image-of-t1-in-new
                         (unless (term-equational-equal image-of-t1-in-new t2)
                           (return-from the-end t))
                       (add-equation-to-environment new-env eq))))))
              (check-match
               (when (term-is-variable? t2)
                 (return-from the-end t))
               (if (and (term-is-applform? t2)
                        (term-is-applform? t1))
                   (let ((t1-head (term-head t1))
                         (t2-head (term-head t2)))
                     (if (method-is-of-same-operator+ t1-head t2-head)
                         (add-equation-to-m-system new-sys eq)
                       (let ((match-info (method-theory-info-for-matching! t1-head)))
                         (if (test-theory .Z. (theory-info-code match-info))
                             (add-equation-to-m-system new-sys eq)
                           (progn
                             (return-from the-end t))))))
                 (add-equation-to-m-system new-sys eq)))
              ;;
              (t (add-equation-to-m-system new-sys eq)))))

    ;; add now all the equation of test-env into new-env (copy test-env)
    (cond ((null (car test-env)) ())
          ((null (car new-env))
           (let ((l (environment-copy1 test-env)))
             (rplaca new-env (car l))
             (rplacd new-env (cdr l))) )
          (t (nconc new-env test-env)))
    nil                                 ; i.e. the new-env is coherent
    ))
||#

;;; MATCH-SYSTEM ===========================================================
;;;
;;; The pair of environment and m-system .
;;;
(defstruct (match-system
             (:constructor create-match-system (environment system-to-solve)))
  (environment (new-environment) :type list)    
  (system-to-solve (new-m-system) :type list))

(defmacro match-system-sys (ms___?) `(match-system-system-to-solve ,ms___?))
(defmacro match-system-env (ms___?) `(match-system-environment ,ms___?))

;;; returns the substitution associated to the m-system "m-s" which is supposed
;;; to be fully solved, that is such that "m-s.sys" is empty and merged.
;;;
(defmacro match-system-to-substitution (?_m-s_?)
  `(environment-to-substitution (match-system-env ,?_m-s_?)))

;;; PRINT UTILS

(defun print-match-system (s)
  (princ "[match-system system:") (print-next)
  (print-match-equations (match-system-sys s))
  (princ "environment:") (print-next)
  (print-match-equations (match-system-env s)) (princ "]")
  )

(defun print-match-system-sys (sys)
  (princ "[match-system-sys:")
  (print-next)
  (print-match-equations sys)
  (princ "]")
  (force-output)
  (finish-output))

(defun print-match-system-env (env)
  (princ "[match-system-env:")
  (print-next)
  (print-match-equations env)
  (princ "]")
  (force-output)
  (finish-output))

(defun print-match-equations (eqs)
  (dolist (e eqs)
    (if (null e) (princ "NIL")
        (print-match-equation e))
    (print-next))
  )

(defun print-match-equation (eqn)
  (term-print-with-sort (car eqn))
  (princ " ?=? ")
  (term-print-with-sort (cdr eqn))
  )

;;; NEW-MATCH-SYSTEM : term1 term2 -> match-system
;;; assuming that given terms are constructs of the one of the two types of the
;;; match-system, creates a new match-system-
(declaim (inline new-match-system))
(defun new-match-system (term1 term2)
  (declare (type term term1 term2)
           (values match-system))
  (if (term-is-variable? term1)
      (create-match-system (create-environment term1 term2)
                           (new-m-system))
    (create-match-system (new-environment)
                         (create-m-system term1 term2))))

;;; returns from a match-system a system (equivalent)
;;;
(defmacro match-system-to-m-system (__?m-sys?)
  (once-only (__?m-sys?)
    ` (make-m-system (m-system-to-list (match-system-sys ,__?m-sys?))
                     (environment-to-list (match-system-env ,__?m-sys?)))))


;;; MATCH-SYSTEM-E-EQUAL : math-system -> bool
;;; returns t iff all of the equations in match-system are composed of
;;; equationaly equal terms.   
;;;
(defun match-system-e-equal (match-system)
  (declare (type match-system match-system)
           (values (or t null)))
  (and (dolist (eq (m-system-to-list (match-system-sys match-system)) t)
         (unless (term-equational-equal (equation-t1 eq) (equation-t2 eq))
           (return nil)))
       (dolist (eq (environment-to-list (match-system-environment match-system)) t)
         (unless (term-equational-equal (equation-t1 eq) (equation-t2 eq))
           (return nil)))))

;;; add try to returns a NEW match-system containing the (set) union of "sys"
;;; and "m-sys". For this purpose, it inserts in a new match-system the equation
;;; of "sys" which are compatible with "m-sys". If they are not compatible then
;;; add signals no-match.  
;;; Z: The equations of "sys" are of any kind, i.e. var == term or term == term.
;;; U: Used by "state.next-state".

;;; Note that the arguments of add must not be destroyed or changed.

(defun match-add-m-system (match-system m-sys)
  (block no-match
    (let* ((old-environment (match-system-environment match-system))
           (new-environment (new-environment)) 
           (new-system (new-m-system)))
      ;; then we insert all the equations of "system" in this new system if
      ;; they are compatible with match-system and copy the environment.
      (when (match-insert-if-coherent-with new-environment
                                           old-environment
                                           new-system
                                           (m-system-to-list m-sys)
                                           )
        (return-from no-match (values nil t)))

      (with-match-debug ()
        (format t "~%[Match-add-m-system]: given ---------------~%")
        (print-match-system match-system)
        (format t "~% m-sys")
        (dolist (eq (m-system-to-list m-sys))
          (let ((t1 (equation-t1 eq))
                (t2 (equation-t2 eq)))
            (print-next)
            (princ "t1: ")(term-print-with-sort t1)
            (print-next)
            (princ "t2: ")(term-print-with-sort t2))))

      ;; new-system is modified but not match-system
      (setq new-system (add-m-system new-system (match-system-sys match-system)))
      (let ((nsys (create-match-system new-environment new-system)))
        (with-match-debug ()
          (format t "~%[MATCH-ADD-M-SYSTEM]: generated new sys ----~%")
          (print-match-system nsys))
        (return-from no-match (values nsys nil))))))

;;; Decompose&Merge
;;; Returns the decompose and merging of the given match-system
;;;
(defun match-decompose&merge (m-sys &optional sigma)
  (block no-match
    (let ((sys (match-system-sys m-sys))
          (env (match-system-env m-sys))
          (new-env (new-environment) )
          (new-sys (new-m-system)))
      (declare (type list new-env new-sys))
      (dolist (eq (m-system-to-list sys))
        (multiple-value-bind (eq-list clash-of-symbol)
            (match-decompose-equation (equation-t1 eq) (equation-t2 eq) sigma)
          (if clash-of-symbol
              (return-from no-match (values nil t))
            (when (match-insert-if-coherent-with new-env 
                                                 env 
                                                 new-sys 
                                                 eq-list)
              (return-from no-match (values nil t))))))
      (let ((msys (create-match-system new-env new-sys)))
        (with-match-debug ()
          (format t "~%[Match-Decompose&Merge]: match system created: ----~%")
          (print-match-system msys))
        (values msys nil)))))


;;; Extracts from the non fully decomposed part of "m-s" the biggest system to
;;; be solved into the theory "th". "th" and "sys" are returned.
;;
(defun match-system-extract-one (m-s)
  (declare (inline m-system-extract-one-system))
  (let ((sys (match-system-sys m-s)))
    (if (m-system-is-empty? sys) 
        (values nil (theory-info *the-empty-theory*))
        (m-system-extract-one-system sys))))

;;; returns a new match-system with the same environment that "m-sys" but with a
;;; system equal to the system of m-sys except the elements in "sys". 
;;; Z: "sys" is supposed included into the system of "m-sys".
;;;
(defun match-system-modif-m-sys (m-sys sys)
  (declare (type match-system m-sys)
           (type list sys)
           (values match-system))
  (flet ((difference-eq (x y)
           (let ((res nil))
             (dolist (xe x res)
               (unless (dolist (ye y nil) (when (eq xe ye) (return t)))
                 (push xe res))))))
    (create-match-system (environment-copy1 (match-system-env m-sys)) 
                         (difference-eq (m-system-to-list (match-system-sys m-sys))
                                        sys))))

;;; EOF

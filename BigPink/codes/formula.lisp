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
                          File:formula.lisp
=============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;;*****************************************************************************
;;;                     ALL ABOUT FOPL FORMULA
;;;*****************************************************************************

(defvar *debug-formula* nil)
(declaim (special *debug-formula-nest*)
         (type fixnum *debug-formula-nest*))
(defvar *debug-formula-nest* 0)

;;;** golobals moved to `glob.lisp'
;;; top-level switch (?) -- may be later.
;;; if t, simplifies formula during formula to clause translation by 
;;; - conflict tautology (ex. p|~p|q --> q)
;;; - discarding weaker conjuncts (ex. (p|q) & (p|q|r) --> p|q)
;;; - discarding stronger disjuncts (ex. (p&q)|(p&q&r) --> p&q)
;;; now defined in `glob.lisp'
;;; (pn-flag simplify-fol)

;;; binds last proccessed list of clause, i.e., return value of
;;; the function `formula->clause-1'
;;; now defined in `glob.lisp'
;;; (defvar $$raw-clause nil)

;;;
;;;
;;;
(defun pn-term-equational-equal (t1 t2)
  (declare (type term t1 t2)
           (values (or null t)))
  (or (term-eq t1 t2)
      (let ((t1-body (term-body t1))
            (t2-body (term-body t2)))
        (cond ((term$is-applform? t1-body)
               (let ((f1 (term$head t1-body)))
                 ;; (break)
                 (if (theory-info-empty-for-matching
                      (method-theory-info-for-matching f1))
                     (match-with-empty-theory t1 t2)
                     (E-equal-in-theory (method-theory f1) t1 t2)))
               )
              ((term$is-builtin-constant? t1-body)
               (term$builtin-equal t1-body t2-body))
              ((term$is-builtin-constant? t2-body) nil)
              ;;
              ((term$is-variable? t1-body)
               (setq *used==* t)
               (or (eq t1-body t2-body)
                   (and (term$is-variable? t2-body)
                        (eq (variable$name t1-body) (variable$name t2-body))
                        (eq (term$sort t1-body) (term$sort t2-body)))
                   ))
              ((term$is-variable? t2-body)
               (setq *used==* t)
               nil)
              ((term$is-lisp-form? t1-body)
               (and (term$is-lisp-form? t2-body)
                    (equal (term$lisp-code-original-form t1-body)
                           (term$lisp-code-original-form t2-body))))
              (t (break "pn-term-equational-equal: not-implemented ~s" t1))
              ))))

;;; ========================================
;;; FOPL FORMULA --> CLAUSE FORM TRANSLATION
;;; ========================================

;;; FORMULA->CLAUSE-1 : FoplSentence -> LIST[Clause]
;;; given a fopl sentence translates it to list of clauses.
;;; 
(declaim (special *current-formula*)
         (type (or null term) *current-formula*))
(defvar *current-formula* nil)

(defun formula->clause-1 (sentence psys &optional (axiom nil))
  (declare (type (or null term) sentence)
           (type psystem psys)
           (type (or null axiom) axiom)
           (values list))
  (if sentence
      (let ((*current-formula* sentence))
        ;; translate to Conjunctive Normal Form.
        (cnf sentence psys)
        ;; to clause list
        (setq $$raw-clause (cnf-to-list sentence psys))
        ;;
        (dolist (cl $$raw-clause)
          (setf (clause-axiom cl) axiom)
          (cl-unique-variables cl))
        $$raw-clause)
    nil))

;;; CNF : FoplSentence -> FoplSentence'
;;; makes Conjuncitve Normal Form.
;;;
(defun cnf (sentence psys)
  (declare (type term sentence)
           (type psystem psys)
           (values term))
  (when *debug-formula*
    (format t "~%** start formula to cnf translation **")
    (print-next)
    (with-in-module ((psystem-module psys))
      (term-print sentence)))
  ;; assumes input sentence is valid formula
  ;; (check-fopl-syntax sentence)
  (let ((type (fopl-sentence-type sentence)))
    (declare (type symbol type))
    (when (and (memq type '(:eq :beq))
               (term-is-lisp-form? (term-arg-2 sentence)))
      (return-from cnf sentence)))

  ;; normalize quantified formula
  ;; \Q[v1...vn]S --> \Q[v1]\Q[v2]...\Q[vn]S
  (normalize-quantifiers sentence)

  ;; convert to NNF(negation normal form.)
  (setq sentence
    (neg-normal-form sentence))

  ;; skolemization -- eliminate \Es
  (skolemize sentence)
  ;; skolemize may introduce new operators.
  (prepare-for-parsing (psystem-module psys))

  ;; make all universally quantified variables unique.
  (unique-all-variables sentence)
  
  ;; eliminate quantifiers -- eliminate \As
  (zap-quantifiers sentence)

  ;; convert to CNF(conjunctive normal form).
  (conj-normal-form sentence)
  (when *debug-formula*
    (format t "~%*** done ***"))
  sentence
  )

;;; NNF-SKOLEMIZE
;;; a little utils for testing. 
;;; skolemize then apply nnf.
(defun nnf-skolemize (sentence)
  (declare (type term sentence)
           (values term))
  (check-fopl-syntax sentence)
  (unique-all-variables 
   (skolemize (neg-normal-form (normalize-quantifiers sentence))))
  sentence)

;;; CAFEOBJ-TERM->FORMULA : Term -> Term
;;;
;;; NOTE: brand new term of FOPL form will be returned.
;;;
(defun cafeobj-term->formula (f)
  (declare (type term f)
           (values term))
  (when *debug-formula*
    (format t "~%[cafeobj-term->formula]: ")
    (term-print f))
  (let ((res nil))
    (declare (type (or null term) res))
    (cond ((term-is-application-form? f)
           (let ((args (mapcar #'(lambda (x) (cafeobj-term->formula x))
                               (term-subterms f)))
                 (head (term-head f)))
             (declare (type list args)
                      (type method head))
             (setq f (make-applform-simple (term-sort f)
                                           head
                                           args))
             (cond ((memq head (list *bool-equal* *beh-equal* *eql-op*))
                    #||
                    (when (eq head *beh-eq-pred*)
                      (with-output-chaos-warning ()
                        (format t "=*= cannot be used: ")
                        (term-print f)))
                    ||#
                    (setq res 
                      (make-term-with-sort-check *fopl-eq*
                                                 (list (term-arg-1 f)
                                                       (term-arg-2 f)))))
                   ((eq head *bool-nonequal*)
                    (setq res
                      (make-term-with-sort-check
                       *fopl-neg*
                       (list
                        (make-term-with-sort-check *fopl-eq*
                                                   (list (term-arg-1 f)
                                                         (term-arg-2 f)))))))
                   ((memq head (list *bool-and*
                                     *bool-or*
                                     *bool-imply*
                                     *bool-iff*
                                     *bool-and-also*
                                     *bool-or-else*
                                     ))
                    (setq res
                      (make-term-with-sort-check
                       (if (or (eq head *bool-and*)
                               (eq head *bool-and-also*))
                           *fopl-and*
                         (if (or (eq head *bool-or*)
                                 (eq head *bool-or-else*))
                             *fopl-or*
                           ;; *bool-imply*
                           (if (eq head *bool-imply*)
                               *fopl-imply*
                             ;; else *bool-iff*
                             *fopl-iff*)
                           ))
                       (list (term-arg-1 f)
                             (term-arg-2 f))))
                    (when (or (eq head *bool-and-also*)
                              (eq head *bool-or-else*))
                      (with-output-chaos-warning ()
                        (format t "operator ~{~a~} is appeared in FOPL sentence, replacing..."
                                (method-symbol head))))
                    )
                   ;;
                   ((eq head *bool-not*)
                    (setq res
                      (make-term-with-sort-check
                       *fopl-neg*
                       (list (term-arg-1 f)))))
                   ((eq head *bool-xor*)
                    ;; p xor q --> (~p | ~q)&(p | q)
                    (setq res
                      (make-term-with-sort-check
                       *fopl-and*
                       (list
                        (make-term-with-sort-check
                         *fopl-or*
                         (list
                          (make-term-with-sort-check
                           *fopl-neg*
                           (list (term-arg-1 f)))
                          (make-term-with-sort-check
                           *fopl-neg*
                           (list (term-arg-2 f)))))
                        (make-term-with-sort-check
                         *fopl-or*
                         (list (allocate-new-term-cell (term-arg-1 f))
                               (allocate-new-term-cell (term-arg-2 f))))))
                      ))
                   ;;;
                   #||
                   ((eq head *bool-if*)
                    (when (and (sort= (term-sort (term-arg-1 f)) *bool-sort*)
                               (sort= (term-sort (term-arg-2 f)) *bool-sort*))
                      ))
                   ||#
                   ;;;
                   ((memq head (list *bool-if*
                                     *beh-eq-pred*
                                     ;; *bool-and-also*
                                     ;; *bool-or-else*
                                     *sort-membership*))
                    (with-output-chaos-warning ()
                      (format t "you cannot use ~a: " (method-symbol head))
                      (term-print f))
                    (setq res (copy-term-reusing-variables f
                                                           (term-variables f))))
                   ;;
                   (t (setq res
                        (copy-term-reusing-variables f
                                                     (term-variables f)))))
             ))
          ;;
          ((term-is-variable? f)
           (setq res f))
          ;;
          (t (setq res (simple-copy-term f))))
    (when *debug-formula*
      (print-next)
      (term-print res))
    res))

;;; NORMALIZE-QUANTIFIERS : Sentence -> Sentence'
;;; - \Q[X1,...,Xn]S ---> \Q[X1]\Q[X2]...\Q[Xn]S
;;;   
(defun normalize-quantifiers (form)
  (declare (type term form))
  (let ((bound-vars nil)
        (all-vars (term-variables form))
        (free-vars nil)
        (res nil))
    (declare (type list bound-vars all-vars free-vars)
             (type (or null term) res))
    (labels ((nq (sentence)
               (let ((type (fopl-sentence-type sentence))
                     (*debug-formula-nest* (1+ *debug-formula-nest*)))
                 (declare (type symbol type))
                 (when *debug-formula*
                   (format t "~%~d>[normalize-quantifiers]: "
                           *debug-formula-nest*)
                   (term-print sentence))
                 (case type
                   (:atom)              ; nothing to do
                   ((:forall :exists)
                    (let ((vardecls (term-arg-1 sentence)))
                      (cond ((term-is-variable? vardecls)
                             (pushnew vardecls bound-vars
                                      :test #'variable-eq)
                             sentence)
                            (t (let ((vars (reverse (term-variables vardecls)))
                                     (new-form nil))
                                 (dolist (v vars)
                                   (pushnew v bound-vars :test #'variable-eq))
                                 (setq new-form
                                   (make-term-with-sort-check
                                    (if (eq type :forall)
                                        *fopl-forall*
                                      *fopl-exists*)
                                    (list (car vars)
                                          (term-arg-2 sentence))))
                                 (dolist (v (cdr vars))
                                   (setq new-form
                                     (make-term-with-sort-check
                                      (if (eq type :forall)
                                          *fopl-forall*
                                        *fopl-exists*)
                                      (list v new-form))))
                                 (term-replace sentence new-form)
                                 ))))
                    ;; recurse
                    (nq (term-arg-2 sentence))
                    )
                   (:not (nq (term-arg-1 sentence)))
                   (otherwise
                    (nq (term-arg-1 sentence))
                    (nq (term-arg-2 sentence))
                    ))
                 ;;
                 (when *debug-formula*
                   (format t "~%<~d " *debug-formula-nest*)
                   (term-print sentence))
                 ;;
                 sentence)))
      ;;
      (setq res (nq form))
      (setq free-vars (set-difference all-vars
                                      bound-vars
                                      :test #'variable-eq))
      (when free-vars
        (let ((new-form (copy-term-reusing-variables
                         (make-universal-closure free-vars res)
                         all-vars)))
          (term-replace res new-form)))
      )))
                                      
(defun make-universal-closure (var-list sentence)
  (declare (type list var-list)
           (type term))
  (let ((res nil))
    (declare (type (or null term) res))
    (dolist (var var-list)
      (declare (type term var))
      (if res
          (setq res (make-term-with-sort-check *fopl-forall*
                                               (list var res)))
        (setq res (make-term-with-sort-check *fopl-forall*
                                             (list var sentence)))))
    res))

;;; NETGATE-SENTENCE : Sentence -> Sentence
;;; - given sentence is changed to its negation.
;;; - does not move negation signs inward.
;;; returns negated sentence
;;;
(defun negate-sentence (sentence &optional copy variables)
  (declare (type term sentence)
           (type list variables))
  (let ((type (fopl-sentence-type sentence)))
    (declare (type symbol type))
    (when *debug-formula*
      (with-output-msg()
        (princ "> negate-sentence: ")
        (term-print sentence)))
    (case type
      (:not
       (let ((new-term (if copy
                           (copy-term-reusing-variables (term-arg-1
                                                         sentence)
                                                        variables)
                         (allocate-new-term-cell (term-arg-1 sentence)))))
         ;; (term-replace sentence new-term)
         (setq sentence new-term)))
      (otherwise
       (let ((new-term (make-term-with-sort-check
                        *fopl-neg*
                        (list (if copy
                                  (copy-term-reusing-variables sentence variables)
                                (allocate-new-term-cell sentence))))))
         ;; (term-replace sentence new-term)
         (setq sentence new-term)
         )))
    (when *debug-formula*
      (with-output-msg ()
        (princ "< negate-sentence: ")
        (term-print sentence)))
    sentence))

;;; NEG-NORMAL-FORM : Sentence -> Sentence'
;;; - translate given Sentence to negation normal form (NNF) by
;;;   removing -> and <->,
;;; - and moving negation all the way in.
;;;
;;; *NOTE: we prefer conjunction
;;;  (A <-> B) -----> ((~A | B)&(~B | A))
;;; ~(A <-> B) -----> ((A | B)&(~A | ~B))
;;;
;;; *ASSUMPTION: given sentence is a really FoplSentence.
;;; *CAUTION: given Sentence will be destructively modified unless
;;;           it is an atomic formula.

(defun neg-normal-form (sentence &optional variables)
  (declare (type term sentence)
           (type list variables))
  (let ((type (fopl-sentence-type sentence))
        (*debug-formula-nest* (1+ *debug-formula-nest*)))
    (declare (type symbol type))
    (when *debug-formula*
      (format t "~%~d>[neg-normal-form]: "
              *debug-formula-nest*)
      (term-print sentence))
    (case type
      (:atom sentence)
      ;; A <-> B ---> neg-normal-form((~A | B) & (~B | A))
      (:iff
       (let ((old-arg1 (allocate-new-term-cell (term-arg-1 sentence))) ; A
             (old-arg2 (allocate-new-term-cell (term-arg-2 sentence)))) ; B
         (let* ((new-arg1               ; ~A | B
                 (make-term-with-sort-check
                  *fopl-or*
                  (list (negate-sentence old-arg1 :copy variables) ; ~A
                        (copy-term-reusing-variables old-arg2 ; B
                                                     variables)
                        )))
                (new-arg2
                 (make-term-with-sort-check
                  *fopl-or*
                  (list (negate-sentence old-arg2 :copy variables) ; ~B
                        (copy-term-reusing-variables (term-arg-1 sentence)
                                                     variables) ; A
                       ))))
           (term-replace sentence
                         (make-term-with-sort-check
                          *fopl-and*
                          (list new-arg1 new-arg2)))
           (neg-normal-form sentence variables)
           sentence)))
      ;;  A -> B ---> neg-normal-form(~A | B)
      (:imply
       (term-replace
        sentence
        (make-term-with-sort-check 
            *fopl-or*
            (list (negate-sentence (term-arg-1 sentence) :copy variables)
                  (copy-term-reusing-variables (term-arg-2 sentence)
                                               variables))))
       (neg-normal-form sentence variables)
       sentence)
      ;; \A[Vars]Formula ---> \A[Vars] neg-normal-form(Formula)
      ;; same as for \E
      ((:forall :exists)
       (setf (term-arg-2 sentence)
         (neg-normal-form (term-arg-2 sentence) variables))
       sentence)
      ;; A & B ---> neg-normal-form(A) & neg-normal-form(B)
      ;; same as for |
      ((:and :or :eq :beq)
       (setf (term-arg-1 sentence)
         (neg-normal-form (term-arg-1 sentence) variables))
       (setf (term-arg-2 sentence)
         (neg-normal-form (term-arg-2 sentence) variables))
       sentence)
      ;; not
      (:not
       (let* ((arg (term-arg-1 sentence))
              (arg-type (fopl-sentence-type arg)))
         (case arg-type
           ;; 
           (:atom 
            ;; *******************
            (when (term-is-applform? arg)
              (if (is-true? arg)
                  (term-replace sentence (new-term *bool-false*))
                (if (is-false? arg)
                    (term-replace sentence (new-term *bool-true*)))))
            ;; *******************
            sentence)
                
           ;; ~(A -> B) --> neg-normal-form(~(~A | B))
           (:imply
            (setf (term-arg-1 sentence)
              (make-term-with-sort-check
               *fopl-or*
               (list (negate-sentence (term-arg-1 arg) :copy variables)
                     (allocate-new-term-cell (term-arg-2 arg)))))
            (neg-normal-form sentence variables)
            sentence)
           ;; ~(A <-> B) --> neg-normal-form((A|B) & (~A |  ~B))
           (:iff
            (let ((old-arg1 (allocate-new-term-cell (term-arg-1 arg)))
                  (old-arg2 (allocate-new-term-cell (term-arg-2 arg))))
              (term-replace
               sentence
               (make-term-with-sort-check
                *fopl-and*
                (list
                 (make-term-with-sort-check ; A | B
                  *fopl-or*
                  (list old-arg1 old-arg2))
                 (make-term-with-sort-check ; ~A | ~B
                  *fopl-or*
                  (list (negate-sentence (term-arg-1 arg) :copy variables)
                        (negate-sentence (term-arg-2 arg) :copy variables))))))
              (neg-normal-form sentence variables)
              sentence))
           ;; ~\A[Vars]S --> \E[Vars]neg-normal-form(~S)
           ;; ~\E[Vars]S --> \A[Vars]neg-normal-form(~S)
           ((:forall :exists)
            (term-replace sentence
                          (make-term-with-sort-check
                           (if (eq arg-type :forall)
                               *fopl-exists*
                             *fopl-forall*)
                           (list (allocate-new-term-cell
                                  (term-arg-1 arg)) ; var list
                                 (neg-normal-form (negate-sentence
                                                   (term-arg-2 arg)
                                                   nil
                                                   variables)
                                                  variables))))
            sentence)
           ;; ~(A & B) --> neg-normal-form(~A) | neg-normal-form(~B)
           ;; ~(A | B) --> neg-normal-form(~A) & neg-normal-form(~B)
           ((:and :or)
            (term-replace sentence
                          (make-term-with-sort-check
                           (if (eq arg-type :and)
                               *fopl-or*
                             *fopl-and*)
                           (list
                            (neg-normal-form (negate-sentence (term-arg-1 arg)
                                                     :copy variables)
                                    variables)
                            (neg-normal-form (negate-sentence (term-arg-2 arg)
                                                     :copy variables)
                                    variables))))
            sentence)
           ;; ~~A --> neg-normal-form(A)
           (:not                        ; double negation
            (term-replace sentence
                          (neg-normal-form (term-arg-1 arg) variables))
            sentence)
           )))
      )
    ;;
    (when *debug-formula*
      (format t "~%~d< " *debug-formula-nest*)
      (term-print sentence))
    ;;
    sentence))

;;; SKOLEMIZE : Sentence -> Sentence'
;;; - Skolemize a formula, i.e., existential quantifiers are deleted,
;;;   and old existentially qulified variables are replaced by skolem 
;;;   function applications.
;;;
;;; *Assumption: given sentence is in negation normal form
;;;
(defun make-skolem-function-name (sort variables)
  (declare (type sort* sort)
           (type list variables))
  (let* ((sname (sort-name sort))
         (num-ent (assq sname *sk-function-num*))
         (num nil))
    (declare (type symbol sname)
             (type list num-ent)
             (type (or null fixnum) num))
    (if num-ent
        (progn
          (setq num (the fixnum (cdr num-ent)))
          (incf (the fixnum (cdr num-ent))))
      (progn
        (push (cons sname 2) *sk-function-num*)
        (setq num 1)))
    (if variables
        (format nil "#f~d@~a" (the fixnum num) (string sname))
      (format nil "#c~d@~a" (the fixnum num) (string sname)))
    ))

(defun skolemize (formula)
  (declare (type term formula)
           (values term))
  (let ((variables nil))
    (declare (type list variables))
    (labels ((skolem (sentence)
               (declare (type term sentence))
               ;; skolemize given sentence w.r.t universally quantified
               ;; vars (assumes `variables' holds them).
               (let ((type (fopl-sentence-type sentence)))
                 (declare (type symbol type))
                 (case type
                   ((:and :or)
                    (skolem (term-arg-1 sentence))
                    (skolem (term-arg-2 sentence)))
                   (:forall
                    (when (member (term-arg-1 sentence) variables
                                  :test #'variable=)
                      ;; rename current variable, because we are
                      ;; already in the scope of universaly quantified
                      ;; variable with that name and sort.
                      (let ((new-var (pn-make-new-variable (term-arg-1 sentence))))
                        ;; in our setting, all variables are shared,
                        ;; thus we must make brand new variables here.
                        ;; and substitute every occurences with the
                        ;; new one.
                        (rename-free-formula (term-arg-2 sentence)
                                             (term-arg-1 sentence)
                                             new-var)
                        (setf (term-arg-1 sentence) new-var)))
                    ;; entry current bound variable
                    (push (term-arg-1 sentence) variables)
                    (skolem (term-arg-2 sentence))
                    ;; delete current var 
                    (pop variables))
                   (:exists
                    ;; must skolemize subformula first to avoid
                    ;; problem in \Ax...\Ey...\Ex F(x,y)
                    (skolem (term-arg-2 sentence))
                    (let* ((mod (get-context-module))
                           (skfun-name
                            (make-skolem-function-name (term-sort
                                                        (term-arg-1 sentence))
                                                       variables)))
                      (multiple-value-bind (op meth)
                          (declare-operator-in-module
                           (list skfun-name)
                           (mapcar #'(lambda (x)
                                       (variable-sort x))
                                   (reverse variables))
                           (variable-sort (term-arg-1 sentence))
                           mod
                           nil          ; constructor?
                           nil          ; behavioural? always nil.
                           ;; set coherent iff having hidden sort arguments
                           (some #'(lambda (x)
                                     (sort-is-hidden (variable-sort x)))
                                 variables)
                           )
                        (declare (ignore op))
                        ;; we may need to check given operation is a 
                        ;; skolem function at later stages.
                        (pushnew meth (module-skolem-functions mod) :test #'eq)
                        ;;
                        (let ((sk-form (make-term-with-sort-check
                                        meth
                                        (reverse variables))))
                          (term-replace sentence
                                        (subst-free-formula (term-arg-2 sentence)
                                                            (term-arg-1 sentence)
                                                            sk-form))
                          ))))

                   ;; following cases handles bad situations.
                   ;; given sentence should be a NNF.
                   (:not
                    (unless (memq (fopl-sentence-type (term-arg-1 sentence))
                                  '(:atom :eq :beq))
                      (with-output-chaos-error ('invalid-formula)
                        (princ "skolemize gets negated non-atom")
                        (term-print sentence)))
                    sentence)
                   ((:imply :iff)
                    (with-output-chaos-error ('invalid-formula)
                      (princ "skolemize gets: ")
                      (term-print sentence)))
                   ;; atom.
                   (otherwise sentence))
                 ;; done
                 sentence)))
      ;;
      (skolem formula)
      )))

;;; RENAME-FREE-FORMULA : sentence old new -> sentence'
;;; - rename free occurrences of variable old in sentence to new.
;;;
(defun rename-free-formula (sentence old new)
  (declare (type term sentence old new))
  (let ((type (fopl-sentence-type sentence)))
    (declare (type symbol type))
    (case type
      ((:forall :exists)
       (unless (variable-eq (term-arg-1 sentence) old)
         (rename-free-formula (term-arg-2 sentence) old new)))
      (otherwise
       (subst-free-term sentence old new)))))

;;; SUBST-FREE-FORMULA : sentence form -> sentence'
;;; 
(defun subst-free-formula (sentence var form)
  (declare (type term sentence var form)
           (values term))
  (let ((type (fopl-sentence-type sentence)))
    (declare (type symbol type))
    (case type
      (:atom
       (subst-free-term sentence var form)
       sentence)
      ((:forall :exists)
       (when (variable-eq var (term-arg-1 sentence))
         (setf (term-arg-1 sentence) form))
       (subst-free-formula (term-arg-2 sentence) var form))
      ((:and :or)
       (subst-free-formula (term-arg-1 sentence)
                           var form)
       (subst-free-formula (term-arg-2 sentence) var form))
      (:not
       (subst-free-formula (term-arg-1 sentence) var form))
      (:eq
       (subst-free-term sentence var form)
       #||
       (subst-free-formula (term-arg-1 sentence) var form)
       (subst-free-formula (term-arg-2 sentence) var form)
       ||#
       )
      (otherwise
       (with-output-panic-message()
         (princ "illegal formula appeared process subst-free-formula")
         (term-print sentence))))
    sentence))

(defun subst-free-term (term var form)
  (declare (type term term term)
           (values term))
  (when *debug-formula*
    (format t "~%>[subst-free-term]:")
    (term-print term))
  (when (term-is-application-form? term)
    (dotimes (x (length (term-subterms term)))
      (let ((sub (term-arg-n term x)))
        (cond ((term-is-variable? sub)
               (when (variable-eq var sub)
                 (setf (term-arg-n term x)
                   (copy-term-reusing-variables form))))
              (t (subst-free-term sub var form))))))
  (when *debug-formula*
    (format t "~%<[subst-free-term]:")
    (term-print term))
  term)

;;; UNIQUE-ALL-VARIABLES : Sentenece -> Sentence'
;;; - make all universally quantified variables unique.
;;;
;;; *Assumption: sentence is in NNF & Skolemized.
;;;
(defun unique-all-variables (sentence)
  (declare (type term sentence))
  (let ((variables nil))
    (declare (type list variables))
    (labels ((unique (f)
               (declare (type term f))
               (let ((type (fopl-sentence-type f)))
                 (declare (type symbol type))
                 (when *debug-formula*
                   (format t "~%>[unique-all-variables]: ~a" type)
                   (term-print f))
                 (case type
                   (:atom)              ; do nothing
                   ((:not :and :or :eq :beq)
                    (dolist (s (term-subterms f))
                      (unique s)))
                   (otherwise           ; forall
                    (if (member (term-arg-1 f)
                                variables
                                :test #'variable=)
                        ;; rename current variable, because already have a
                        ;; quantified var with that name
                        (let ((new-var (pn-make-new-variable (term-arg-1 f))))
                          (rename-free-formula (term-arg-2 f)
                                               (term-arg-1 f)
                                               new-var)
                          (setf (term-arg-1 f) new-var))
                      ;; else
                      (let ((new-var (pn-make-new-variable
                                      (term-arg-1 f))))
                        (rename-free-formula (term-arg-2 f)
                                             (term-arg-1 f)
                                             new-var)
                        (setf (term-arg-1 f) new-var)
                        (push (term-arg-1 f) variables)))
                    ;; recurse 
                    (unique (term-arg-2 f))
                    ))
                 (when *debug-formula*
                   (format t "~%<[unique-var..]:")
                   (term-print f))
                 )))
      ;;
      (unique sentence)
      sentence)))

;;; ZAP-QUANTIFIERS : Sentence -> Sentence'
;;; - delete quantifiers and mark quantified variables
;;; *Assumption: given sentence is skolemized nnf with unique
;;;              universally quantified variables.
;;;
(defun zap-quantifiers (sentence)
  (declare (type term sentence)
           (values term))
  (let ((type (fopl-sentence-type sentence))
        (*debug-formula-nest* (1+ *debug-formula-nest*)))
    (declare (type symbol type))
    (when *debug-formula*
      (format t "~%~d>[zap-quantifiers]: " *debug-formula-nest*)
      (term-print sentence))
    ;;
    (case type
      ((:not :and :or :eq :beq)
       (map nil #'(lambda (x)
                    (zap-quantifiers x))
            (term-subterms sentence))
       sentence)
      (:forall
       (term-replace sentence (zap-quantifiers (term-arg-2 sentence)))
       sentence)
      (:atom)
      (otherwise
       (with-output-panic-message ()
         (format t "zap-quantifiers accepted illegal formula type ~a: " type)
         (term-print sentence))))
    ;;
    (when *debug-formula*
      (format t "~%~d< " *debug-formula-nest*)
      (term-print sentence))
    sentence))

;;; CONJ-NORMAL-FORM : Sentence -> Sentence'
;;; - convert NNF sentence to CNF (conjuctive normal form).
;;;
;;; *Assumption: sentence is nnf, skolemized, all quantifiers are
;;;              already eliminated.

(defun conj-normal-form (sentence)
  (declare (type term sentence)
           (values term))
  (let ((type (fopl-sentence-type sentence))
        (*debug-formula-nest* (1+ *debug-formula-nest*)))
    (declare (type symbol type))
    (when *debug-formula*
      (format t "~%~d>[cnj-normal-form]: " *debug-formula-nest*)
      (term-print sentence))
    (case type
      ((:and :or)
       ;; convert sub terms to CNF
       (conj-normal-form (term-arg-1 sentence))
       (conj-normal-form (term-arg-2 sentence))
       ;; then itself
       (cond ((eq type :and)
              (when (pn-flag simplify-fol)
                (conflict-tautology sentence)
                (subsume-conjuncts sentence)))
             (t                         ; or
              ;; or ditribution
              (distribute-or sentence))))
      (otherwise sentence))
    (when *debug-formula*
      (format t "~%~d< " *debug-formula-nest*)
      (term-print sentence))
    sentence))

;;; DISTRIBUTE-OR : Sentence -> Sentence'
;;; - distribute or over and.
;;;     A | (B & C) --> (A | B) & (A | C)
;;; *Assumption: given sentence is an OR node, whose
;;;              subterms are already in CNF.
;;; 
(defun distribute-or (sentence)
  (declare (type term sentence)
           (values term))
  (unless (eq :or (fopl-sentence-type sentence))
    (return-from distribute-or sentence))
  (let ((*debug-formula-nest* (1+ *debug-formula-nest*)))
    (when *debug-formula*
      (format t "~%~d>*distribute | over &: "
              *debug-formula-nest*)
      (term-print sentence))
    (when (pn-flag simplify-fol)
      ;; simplify
      (conflict-tautology sentence)
      (subsume-disjuncts sentence))
    ;;
    (unless (eq (fopl-sentence-type sentence) :or)
      (when *debug-formula*
        (format t "~%~d< " *debug-formula-nest*)
        (term-print sentence))
      (return-from distribute-or sentence))
    (let* ((args (gather-subterms-with-top (term-head sentence)
                                           sentence))
           (and-form (find-if #'(lambda (x)
                                  (eq :and
                                      (fopl-sentence-type x)))
                              args)))
      (if and-form
          (setq args (delete and-form args)))
      (unless and-form
        ;; there's no and-form in subterms.
        (when *debug-formula*
          (format t "~%~d< " *debug-formula-nest*)
          (term-print sentence))
        (return-from distribute-or sentence))
      ;;
      (let ((arg-1 (pop args))
            (new-form nil))
        (setq new-form
          (make-term-with-sort-check
           *fopl-and*
           (list (distribute-or
                  (make-term-with-sort-check
                   *fopl-or*
                   (list arg-1          ; known to be not :or form
                         (distribute-or (term-arg-1 and-form))
                         )))
                 (distribute-or
                  (make-term-with-sort-check
                   *fopl-or*
                   (list (copy-term-reusing-variables arg-1)
                         (distribute-or (term-arg-2 and-form))))))))
        (unless args
          (term-replace sentence new-form)
          (when *debug-formula*
            (format t "~%~d< " *debug-formula-nest*)
            (term-print sentence))
          (return-from distribute-or sentence))
        ;;
        (setq new-form
          (make-right-assoc-normal-form-with-sort-check
           *fopl-or*
           (cons new-form args)))
        ;;
        (term-replace sentence
                      (distribute-or (allocate-new-term-cell new-form)))
        (when (pn-flag simplify-fol)
          ;; simplify
          (conflict-tautology sentence)
          (subsume-conjuncts sentence))
        ;;
        (when *debug-formula*
          (format t "~%~d< " *debug-formula-nest*)
          (term-print sentence))
        sentence))))


;;; GATHER-SUBTERMS-WITH-TOP : op sentence -> List[sentence]
;;;
(defun gather-subterms-with-top (op sentence)
  (declare (type method op)
           (type term sentence))
  (list-assoc-subterms sentence op))

;;; CONFLICT-TAUTOLOGY : Sentence -> Sentence'
;;; - if sentence is an and-form, reduce to empty disjunction (false)
;;;   iff conflicting conjuncts occur.
;;;        P & ~P & ... -> false
;;; - if sentence is an or-form, reduce to empty conjunction (true)
;;;   iff conflicting disjuncts occur.
;;;        P | ~P | ... -> true 
;;;
(defun conflict-tautology (sentence)
  (declare (type term sentence)
           (values term))
  (let ((type (fopl-sentence-type sentence))
        (*debug-formula-nest* (1+ *debug-formula-nest*)))
    (declare (type symbol type))
    (unless (or (eq type :and)
                (eq type :or))
      (return-from conflict-tautology sentence))
    ;;
    (when *debug-formula*
      (format t "~%~d>*conflict-tautology: " *debug-formula-nest*)
      (term-print sentence))
    ;;
    (let ((subs (gather-subterms-with-top (term-head sentence)
                                          sentence)))
      (declare (type list subs))
      (let ((org-sub-len (length subs))
            (confliction nil))
        (declare (type fixnum org-sub-len))
        (case type
          (:and (when (find-if #'(lambda (x)
                                   (is-false? x))
                               subs)
                  (setq confliction t))
                (unless confliction
                  (setq subs (remove-if
                              #'(lambda (x)
                                  (is-true? x))
                              subs)))
                )
          (:or (when (find-if #'(lambda (x)
                                  (is-true? x))
                              subs)
                 (setq confliction t))
               (unless confliction
                 (setq subs (remove-if
                             #'(lambda (x)
                                 (is-false? x))
                             subs)))
               ))
        ;;
        (unless confliction
          (dolist (s subs)
            (let ((sign (eq (fopl-sentence-type s) :not)))
              (when (setq confliction
                      (find-if #'(lambda (x)
                                   (and (not (eq s x))
                                        (cond (sign ; s is negation
                                               (pn-term-equational-equal
                                                (term-arg-1 s)
                                                x))
                                              (t ; s is not negation
                                               (and (eq (fopl-sentence-type x)
                                                        :not)
                                                    (pn-term-equational-equal
                                                     s
                                                     (term-arg-1 x)))))))
                               subs))
                (return)))))
        ;;
        (when confliction
          (if (eq type :and)
              (term-replace sentence (new-term *bool-false*))
            (term-replace sentence (new-term *bool-true*)))
          (when *debug-formula*
            (format t "~%<~d: " *debug-formula-nest*)
            (term-print sentence))
          (return-from conflict-tautology sentence)
          )
        ;;
        (unless (= org-sub-len (the fixnum (length subs)))
          (let ((new-form nil))
            (if (cdr subs)
                (setq new-form
                  (make-right-assoc-normal-form
                   (if (eq type :and)
                       *fopl-and*
                     *fopl-or*)
                   subs))
              (if subs
                  (setq new-form (car subs))
                (setq new-form
                  (if (eq type :and)
                      (new-term *bool-true*)
                    (new-term *bool-false*)))))
            (term-replace sentence new-form)))
        ;;
        (when *debug-formula*
          (format t "~%<~d: " *debug-formula-nest*)
          (term-print sentence))
        sentence))))

;;; SUBSUME-CONJUNCTS : Sentence -> Sentence'
;;; - given a conjuction, discard weaker conjuncts.
;;; - the result is guaranteed to be equivalent to the original.
;;;
(defun subsume-conjuncts (c)
  (declare (type term c))
  (unless (eq (fopl-sentence-type c) :and)
    (return-from subsume-conjuncts c))
  (let ((subs (gather-subterms-with-top (term-head c) c))
        (*debug-formula-nest* (1+ *debug-formula-nest*)))
    (declare (type list subs))
    (when *debug-formula*
      (format t "~%~d>*subsume-conjuncts: " *debug-formula-nest*)
      (term-print c))
    (let ((res (copy-list subs)))
      (declare (type list res))
      (dolist (s subs)
        (declare (type term s))
        (if (find-if #'(lambda (x)
                         (and (not (term-eq s x))
                              (gen-subsume-prop x s)))
                     res)
            (setq res (delete s res))
          ;; 
          (setq res (delete-if #'(lambda (x)
                                   (and (not (term-eq s x))
                                        (gen-subsume-prop s x)))
                               res))))
      ;;
      (unless (= (the fixnum (length subs)) (the fixnum (length res)))
        (if (cdr res)
            (let ((new-and-term
                   (make-term-with-sort-check
                    *fopl-and*
                    (list (car res) (cadr res)))))
              (dolist (arg (cddr res))
                (setq new-and-term
                  (make-term-with-sort-check
                   *fopl-and*
                   (list new-and-term arg))))
              (term-replace c new-and-term))
          (term-replace c (car res))))
      ;;
      (when *debug-formula*
        (format t "~%~d< " *debug-formula-nest*)
        (term-print c))
      ;;
      c)))

;;; SUBSUME-DISJUNCTS (d)
;;; - given a disjunction, discard stronger disjuncts.
;;; - the result is eqivalent
;;; the dual of normal clause subsumption.
;;;
(defun subsume-disjuncts (d)
  (declare (type term d)
           (values term))
  (unless (eq (fopl-sentence-type d) :or)
    (return-from subsume-disjuncts d))
  (let ((subs (gather-subterms-with-top (term-head d) d))
        (*debug-formula-nest* (1+ *debug-formula-nest*)))
    (declare (type list subs))
    (when *debug-formula*
      (format t "~%~d>*subsume-disjuncts: " *debug-formula-nest*)
      (term-print d))
    ;;
    (let ((res (copy-list subs)))
      (declare (type list res))
      (dolist (s subs)
        (declare (type term s))
        (if (find-if #'(lambda (x)
                         (and (not (term-eq s x))
                              (gen-subsume-prop s x)))
                     res)
            (setq res (delete s res))
          (setq res (delete-if #'(lambda (x)
                                   (and (not (term-eq x s))
                                        (gen-subsume-prop x s)))
                               res))))
      (unless (= (the fixnum (length res)) (the fixnum (length subs)))
        (if (cdr res)
            (let ((new-or-term
                   (make-term-with-sort-check
                    *fopl-or*
                    (list (car res) (cadr res)))))
              (dolist (arg (cddr res))
                (setq new-or-term
                  (make-term-with-sort-check
                   *fopl-or*
                   (list new-or-term arg))))
              (term-replace d new-or-term))
          (term-replace d (car res))))
      ;;
      (when *debug-formula*
        (format t "~%~d< " *debug-formula-nest*)
        (term-print d))
      ;;
      d)))

;;; GEN-SUBSUME-PROP : c d -> bool
;;; - a generalized propositional subsumption.
;;; - returns t iff c subsumes d.
;;; - quantified formulas are treated as atoms.
;;;
(defvar *debug-subsume-prop* nil)
(declaim (special *debug-subsume-prop-nest*))
(defvar *debug-subsume-prop-nest* 0)

(defun gen-subsume-prop (c d)
  (declare (type term c d))
  (let ((c-type (fopl-sentence-type c))
        (d-type (fopl-sentence-type d)))
    (declare (type symbol c-type d-type))
    (let ((res nil)
          (*debug-subsume-prop-nest* (1+ *debug-subsume-prop-nest*)))
      (when *debug-subsume-prop*
        (format t "~%~d>[subsume prop]: " *debug-subsume-prop-nest*)
        (format t "~&c = ")(term-print c)
        (format t "~&d = ")(term-print d))
      (setq res
        (if (eq c-type :or)
            ;; test each c_i subsumes d
            (every #'(lambda (x)
                       (or (is-true? x)
                           (gen-subsume-prop x d)))
                   (term-subterms c))
          ;; c-type = :and or others
          (if (eq d-type :and)
              ;; test c subsumes each d_i
              (every #'(lambda (x)
                         (gen-subsume-prop c x))
                     (term-subterms d))
            (if (eq c-type :and)
                ;; test one c_i subsumes d
                (some #'(lambda (x)
                          (or (is-false? x)
                              (gen-subsume-prop x d)))
                      (term-subterms c))
              (if (eq d-type :or)
                  ;; test c subsumes one d_i
                  (some #'(lambda (x)
                            (gen-subsume-prop c x))
                        (term-subterms d))
                ;; c and d are :not, :atom, :forall, or :exists
                (formula-is-identical c d)
                )))))
      (when *debug-subsume-prop*
        (format t "~%~d< ~a" *debug-subsume-prop-nest* res))
      ;;
      res)))

;;; FORMULA-IS-IDENTICAL : Sentence Sentence -> Bool
;;;
(defun formula-is-identical (s1 s2)
  (declare (type term s1 s2))
  (term-equational-equal s1 s2))

;;; TERM->CLAUSE : Sentence -> Clause
;;;
(defun term->clause (f psys)
  (declare (type term f)
           (type psystem psys))
  (let ((type (fopl-sentence-type f))
        (c (new-clause psys *current-formula*)))
    (declare (type symbol type)
             (type clause c))
    (when *debug-formula*
      (format t "~%>>*term->clause: ")
      (term-print f))
    (when (is-true? f)
      (return-from term->clause nil))
    ;;
    (case type
      ((:atom :not :eq :beq)
       (let ((lit (make-literal :sign (not (eq type :not))
                                :atom (if (not (eq type :not))
                                          f
                                        ;; ~ P
                                        (term-arg-1 f))
                                :clause c)))
         (declare (type literal lit))
         (mark-literal lit)
         (if (is-false? f)
             ;; make empty clause
             (setf (clause-literals c) nil)
           (setf (clause-literals c) (list lit)))))
      ;;
      (:or
       (let ((subs (gather-subterms-with-top (term-head f) f))
             (res nil))
         (declare (type list subs res))
         (dolist (sub subs)
           (let* ((stype (fopl-sentence-type sub))
                  (lit (if (is-false? sub)
                           :false
                         (make-literal :sign (not (eq stype :not))
                                       :atom (if (not (eq stype :not))
                                                 sub
                                               (term-arg-1 sub))
                                       :clause c))))
             (declare (type symbol stype)
                      (type (or symbol literal) lit))
             (push lit res)))
         (setq res (delete :false res :test #'eq))
         (dolist (l res)
           (mark-literal l)
           (push l (clause-literals c)))
         ))
      ;;
      (otherwise (with-output-panic-message ()
                   (format t "term->clause: accepted illegal formula~%")
                   (term-print f))))
    ;; merge identical literals
    (merge-clause c)
    c))

;;; CNF-TO-LIST : Sentence Psystem -> List[Clause]
;;; -- convert a CNF formula to a list of clauses
;;;
(defun cnf-to-list (sentence psys)
  (declare (type term sentence)
           (type psystem psys))
  (let ((stype (fopl-sentence-type sentence))) 
    (declare (type symbol stype))
    (if (eq stype :and)
        (let ((subs (gather-subterms-with-top (term-head sentence)
                                              sentence))
              (res nil))
          (declare (type list subs res))
          (dolist (s subs)
            (declare (type term s))
            (unless (is-true? s)
              (setq res (nconc res
                               (list (term->clause s psys))))))
          res)
      (let ((res (term->clause sentence psys)))
        (declare (type (or null clause) res))
        (if res
            (list res)
          nil))
      )))

;;; EOF

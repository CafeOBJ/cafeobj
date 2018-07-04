;;;-*- Mode: Lisp; Syntax:CommonLisp; Package:CHAOS; Base:10 -*-
;;;
;;; Copyright (c) 2000-2018, Toshimi Sawada. All rights reserved.
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
                           Module: primitives.chaos
                             File: term-utils.lisp
=============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; (defvar *term-debug* nil)

;;; == DESCRIPTION ============================================================
;;; UTILITY PROCS on TERMS
;;; Many routines are based on OBJ3 interpeter of SRI International.
;;; reorganized and adopted to Chaos system by <sawada@sra.co.jp>.

;;;*****************************
;;; Application form constructor________________________________________________
;;;*****************************

(defmacro method-is-object-constructor (__method__)
  `(eq (method-constructor ,__method__) ':object))

(defmacro method-is-record-constructor (__method__)
  `(eq (method-constructor ,__method__) ':record))

(defmacro make-applform-simple (_sort _meth &optional _subterms)
  `(make-application-term ,_meth ,_sort ,_subterms))

(defun make-applform (sort meth &optional args)
  (declare (type sort* sort)
           (type method meth)
           (type list args))
  (make-applform-simple sort meth args))

;;; ******************
;;; RESET-REDUCED-FLAG---------------------------------------------------------
;;; ******************
(defun reset-reduced-flag (term)
  (declare (type term term))
  (when (or (term-is-builtin-constant? term)
            (pvariable-term? term))
    (return-from reset-reduced-flag term))
  (mark-term-as-not-reduced term)
  (when (term-is-application-form? term)
    (dolist (sub (term-subterms term))
      (reset-reduced-flag sub)))
  term)

;;; **************************
;;; WITH-VARIABLE-AS-CONSTANT------------------------------------------------
;;; VARIABLES <-> CONSTANTS
;;; **************************

;;; if T variables are treated as constants
;;; default is nil
(defvar *variable-as-constant* nil)

(defun make-pconst-from-var (var)
  (let ((name (variable-name var))
        (print-name (variable-print-name var))
        (sort (variable-sort var))
        (unique-marker (gensym))
        (pc-name nil)
        (pc-pname nil))
    (setq pc-name (intern (concatenate 'string "`" (string unique-marker) "-" (string name))))
    (if print-name
        (setq pc-pname (intern (concatenate 'string "`" (string print-name))))
      (setq pc-pname pc-name))
    (make-pconst-term sort pc-name pc-pname)))

(defun variables->pconstants (term)
  (let ((vars (term-variables term))
        (subst (new-substitution))
        (rsubst (new-substitution)))
    (dolist (var vars)
      (let ((pc (make-pconst-from-var var)))
        (setq subst (substitution-add subst var pc))
        (setq rsubst (substitution-add rsubst pc var))))
    (setq rsubst (copy-tree rsubst))    ; because substitution-image-no-copy 
                                        ; destructively changes given term
    (substitution-image-no-copy subst term)
    rsubst))

(defun revert-pconstants (term rsubst)
  (substitution-image-no-copy rsubst term :subst-pconstance)
  term)

;;; do some computation with term within a env 
(defmacro with-variable-as-constant ((_term_) &body body)
  (once-only (_term_)
    `(if *variable-as-constant*
         (let ((_rsubst (variables->pconstants ,_term_)))
           (progn
             (block with-variable-as-constant
               ,@body)
             (revert-pconstants ,_term_ _rsubst)
             ,_term_))
       (progn
         (block with-variable-as-it-is
           ,@body)
         ,_term_))))

;;; ****************
;;; ILL FORMED TERMS___________________________________________________________
;;; ****************

;;; TERM is ill defined if it has a sort equal to or less than *syntax-error-sort*.

(defun term-is-an-error (term)
  (declare (type term term)
           (values (or null t)))
  (and (term? term)
       (let ((sort (term$sort (term-body term))))
         (and (not (sort= *bottom-sort* sort))
              (sort<= sort *syntax-err-sort* *chaos-sort-order*)))))

(eval-when (:execute :load-toplevel)                    ; synonym
  (setf (symbol-function 'term-ill-defined)
        (symbol-function 'term-is-an-error)))

;;; Returns true iff the term is application form and has error-method
;;; as its top.
;;;
(defun term-head-is-error (tm)
  (declare (type term tm)
           (values (or null t)))
  (let ((body (term-body tm)))
    (and (term$is-application-form? body)
         (method-is-error-method (appl$head body)))))

;;; Returns true iff the term is application form and has user defined
;;; error method as its top.
;;;
(defun term-head-is-user-defined-error (tm)
  (declare (type term tm)
           (values (or null t)))
  (and (term-is-application-form? tm)
       (method-is-user-defined-error-method (term-head tm))))

;;; TERM-IS-REALLY-WELL-DEFINED tm
;;; returns t iff
;;; (1) the term tm is not ill defined (in terms of `term-ill-defined')
;;;     nor its head method is not a error-method
;;; AND
;;; (2) all of the subterms are TERM-IS-REALY-WELL-DEFINED
;;;
(defun term-is-really-well-defined (term)
  (declare (type term term)
           (values (or null t)))
  (if (term-is-an-error term)
      nil
      (if (term-is-applform? term)
          (if (method-is-error-method (term-head term))
              nil
              (dolist (sub (term-subterms term) t)
                (unless (term-is-really-well-defined sub)
                  (return nil))))
          t)))
    
;;; creats ill-formed terms
;;;

(defun make-directly-ill-term (head subterms)
  (declare (type method head)
           (type list subterms)
           (values term))
  (make-applform-simple *type-err-sort* head subterms))

(defun make-inheritedly-ill-term (head subterms)
  (declare (type method head)
           (type list subterms)
           (values term))
  (make-applform-simple *type-err-sort* head subterms))

;;; TERM-ERROR-OPERATORS&VARIABLES
;;; returns the list of error operators contained in term.
;;;
(defun term-error-operators&variables (term &optional vars-also)
  (declare (type term term)
           (type (or null t) vars-also)
           (values list))
  (let ((res (cons nil nil)))
    (gather-error-methods-and-variables term res vars-also)
    (car res)))

(defun gather-error-methods-and-variables (term res vars-also)
  (declare (type term term)
           (type list res)
           (type (or null t) vars-also)
           (values list))
  (if (term-is-application-form? term)
      (let ((head (term-head term)))
        (if (method-is-error-method head)
            (progn
              (pushnew head (car res) :test #'eq)
              (dolist (sub (term-subterms term))
                (gather-error-methods-and-variables sub res vars-also)))
          (if t ;; (method-is-universal* head)
                (dolist (sub (term-subterms term))
                  (gather-error-methods-and-variables sub res vars-also)))))
      (if (and vars-also (term-is-variable? term))
          (when (err-sort-p (variable-sort term))
            (pushnew term (car res) :test #'eq)))))

;;; test if a appl term contains error-method.

(defun term-contains-error-method (term)
  (declare (type term term)
           (values (or null t)))
  (let ((body (term-body term)))
    (when (term$is-application-form? body)
      (or (method-is-error-method (appl$head body))
          (some #'term-contains-error-method (term$subterms body))))))


;;; test if a appl form contains user defined error-method.

(defun term-contains-user-defined-error-method (term)
  (declare (type term term)
           (values (or null t)))
  (and (term-is-application-form? term)
       (or (method-is-user-defined-error-method (term-head term))
           (some #'term-contains-user-defined-error-method
                 (term-subterms term)))))

;;; test if a appl form contains match-operator(:=).

(defun term-contains-match-op (term)
  (declare (type term term)
           (values (or null t)))
  (and (term-is-application-form? term)
       (or (method= *bool-match* (term-head term))
           (some #'term-contains-match-op
                 (term-subterms term)))))

;;; test if a appl form contains search predicate which may
;;; introduce new variables
#||
(defparameter sch-op-names
    '(("_" "=" "(" "_" "," "_" ")" "=>+" "_" "if" "_" "suchThat" "_" "{" "_" "}")))

(defun term-contains-sp-sch-predicate (term)
  (and (term-is-application-form? term)
       (or (member (method-symbol (term-head term))
                   sch-op-names
                   :test #'equal)
           (some #'term-contains-sp-sch-predicate
                  (term-subterms term)))))
||#

(defun term-contains-sp-sch-predicate (term)
  (and (term-is-application-form? term)
       (or (eq (method-module (term-head term)) *rwl-module*)
           (some #'term-contains-sp-sch-predicate
                  (term-subterms term)))))

;;; ****************
;;; RECOMPUTING SORT____________________________________________________________
;;; ****************

;;; UPDATE-LOWEST-PARSE : TERM -> TERM'
;;; update sort of the term, possibly head method may change.
;;;
(defun set-if-then-else-sort (term &optional (so *current-sort-order*))
  (when (eq (term-head term)
            *bool-if*)
    (let ((arg2 (term-arg-2 term))
          (arg3 (term-arg-3 term)))
      (unless (is-in-same-connected-component (term-sort arg2)
                                              (term-sort arg3)
                                              so)
        (with-output-chaos-error ('incompatible-sorts)
          (princ "2nd. and 3rd. arguments of if_then_else_fi must be of the same sort.")))
      (update-lowest-parse arg2)
      (update-lowest-parse arg3)
      (if (sort<= (term-sort arg2) (term-sort arg3))
          (setf (term-sort term) (term-sort arg3))
        (setf (term-sort term) (term-sort arg2)))))
  )

(defun select-if-then-least (ifs &optional (so *current-sort-order*))
  (unless (cdr ifs) (return-from select-if-then-least ifs))
  (dolist (x ifs)
    (set-if-then-else-sort x so))
  (let ((result (car ifs)))
    (dolist (ift (cdr ifs))
      (if (sort< (term-sort ift) (term-sort result) so)
          (setq result ift)
        (unless (is-in-same-connected-component (term-sort ift) (term-sort result) so)
          (return-from select-if-then-least ifs))))
    (list result)))

(declaim (special *update-lowest-parse-in-progress*))
(defvar *update-lowest-parse-in-progress* nil)
(defvar *do-assoc-arrangement* t)

(defun update-lowest-parse (term)
  (declare (type term term)
           (values t))
  (let ((body (term-body term))
        (assoc-applied nil))
    (unless (or (pvariable-term? term) (term-is-an-error term))
      (when (term-is-application-form? term)
        (let ((ts (term-sort term))
              (mso (method-coarity (term-head term))))
          (when (sort< mso ts)
            (when *term-debug*
              (with-output-chaos-warning ()
                (format t "something is bad, sort of the term is bigger than top method's coarity.")
              (print-next)
              (format t "Coarity: ")
              (print-sort-name mso *current-module*)
              (print-next)
              (term-print-with-sort term)))
            (setf (term-sort term) mso)
            (when *term-debug*
              (format t "~&[ULP] --> ")
              (term-print-with-sort term)))))
      (if (term$is-builtin-constant? body)
          ;; built-in constant term
          (let* ((isrt (term$sort body))
                 (cm (get-object-context isrt))
                 (so (if cm 
                         (module-sort-order cm)
                       (with-output-chaos-error ('internal-error)
                         (format t "Internal Error, No context module [ULP]."))))
                 (val (term$builtin-value body)))
            (declare (type sort-order so)
                     (type sort* isrt)
                     (type t val))
            (let ((subs (subsorts isrt so))
                  (srt isrt))
              (declare (type list subs)
                       (type sort* srt))
              (dolist (s subs)
                (declare (type sort* s))
                (if (and (sort< s srt so)
                         (sort-is-builtin s)
                         (bsort-term-predicate s)
                         (funcall (bsort-term-predicate  s) val))
                    (setq srt s)))
              (setf (term$sort body) srt)
              term))

        ;; application form
        (let* ((head (appl$head body))
               (mod (get-object-context (method-operator head)))
               (son nil)
               (t1 nil)
               (t2 nil)
               (sort-order (module-sort-order mod))
               (new-head nil))
          (declare (type method head)
                   (type module mod))
          ;; ----------------------------
          ;; special case if_then_else_fi
          ;; ----------------------------
          (when (eq (term-head term) *bool-if*)
            (set-if-then-else-sort term)
            (return-from update-lowest-parse term))

          ;; --------------------------
          ;; "standard" morphism rules
          ;; --------------------------

          (when *term-debug*
            (format t "~&[ULP] given term =====================~%  ")
            (term-print-with-sort term)
            (format t "~&[ULP] current = ")
            (print-chaos-object head))
          (setq new-head
            (lowest-method head
                           (mapcar #'(lambda (x)
                                       (declare (type term x))
                                       (term-sort x))
                                   (term$subterms body))
                           mod))
          (when *term-debug*
            (format t "~&[ULP] new = ")
            (print-chaos-object new-head)
            (untrace))
          ;;
          (when (not (eq head new-head))
            (change-head-operator term new-head)
            (setf (term-sort term) (method-coarity new-head))
            (mark-term-as-not-reduced term)
            ;; (reset-reduced-flag term)        ; ????
            (when *term-debug*
              (format t "~&[ULP] head operator was changed =======")))
          ;;
          (setq head new-head)
          ;;
          (when (and (method-is-associative head)
                     (method-is-commutative head))
            (let ((subs (gather-term-ac-leaf-ordered term)))
              (when *term-debug*
                (dolist (t1 subs)
                  (format t "~%sub: ")
                  (term-print-with-sort t1)))
              (term-replace term 
                            (make-right-assoc-normal-form-with-sort-check (term-head term) subs))
              (when *term-debug*
                (format t "~%[ULP] AC:~%")
                (print-term-tree term t))))

          (when (and (method-is-associative head) *do-assoc-arrangement*)
            ;; &&&& the following transformation tends to put
            ;; term into standard form even when sort doesn't decrease.
            (when (and (not (or (pvariable-term-body? (setq son (term-body
                                                                 (term$arg-1 body))))
                                (term$is-builtin-constant? son)))
                       (method-is-associative-restriction-of (appl$head son) head)
                       (is-in-same-connected-component (term-sort (setq t1 (term$arg-2 son)))
                                                       (term-sort (setq t2 (term$arg-2 body)))
                                                       sort-order))
              (cond ((sort< (term-sort t2)
                            (term-sort (term$arg-1 son))
                            sort-order)
                     (when *term-debug*
                       (format t "~&[ULP] ASSOC1-1")
                       (print-term-tree term t))
                     ;; we are in the following configuration
                     ;;              fs'   ->    fs'
                     ;;          fs'    s     s'     fs
                     ;;       s'    s              s   s
                     ;; so:
                     (setf (term$subterms body)
                       (list (term$arg-1 son)
                             (update-lowest-parse (make-term-with-sort-check-bin head (list t1 t2)))))
                     (when *term-debug*
                       (format t "~%==>")
                       (print-term-tree term t))
                     (setq assoc-applied t))
                    ((and (method-is-commutative head)
                          (sort< (term-sort t2)
                                 (term-sort (term$arg-2 son)) 
                                 sort-order))
                     (when *term-debug*
                       (format t "~&[ULP] ASSOC 1-2")
                       (print-term-tree term t))
                     (setf (term$subterms body)
                       (list (term$arg-2 son)
                             (update-lowest-parse 
                              (make-term-with-sort-check-bin head (list (term$arg-1 son)
                                                                        t2)))))
                     (when *term-debug*
                       (format t "~%==>")
                       (print-term-tree term t))
                     (setq assoc-applied t))))

            ;; would only like to do the following if the
            ;; sort really decreases
            (when (and (not (or (pvariable-term-body? (setq son (term-body
                                                                 (term$arg-2 body))))
                                (term$is-builtin-constant? son)))
                       (method-is-associative-restriction-of (appl$head son) head)
                       (is-in-same-connected-component (term-sort (setq t1 (term$arg-1 body)))
                                                       (term-sort (setq t2 (term$arg-1 son)))
                                                       sort-order))
              (cond ((sort< (term-sort t1) (term-sort (term$arg-2 son)) sort-order)
                     ;; we are in the following configuration
                     ;;              fs'       ->       fs'
                     ;;            s     fs'         fs     s'
                     ;;                s    s'     s   s
                     ;; so:
                     (when *term-debug*
                       (format t "~%[ULP] ASSOC 2-1")
                       (print-term-tree term t))
                     (setf (term-subterms term)
                       (list (update-lowest-parse
                              (make-term-with-sort-check-bin head (list t1 t2)))
                             (term$arg-2 son)))
                     (setq assoc-applied t)
                     (when *term-debug*
                       (print-term-tree term t)))
                    ((and (method-is-commutative head)
                          (sort< (term-sort t1) (term-sort (term$arg-1 son)) sort-order))
                     (when *term-debug*
                       (format t "~&[ULP] ASSOC 2-2")
                       (print-term-tree term t))
                     (setf (term-subterms term)
                       (list (update-lowest-parse
                              (make-term-with-sort-check-bin head (list t1 (term$arg-2 son))))
                             (term$arg-1 son)))
                     (when *term-debug*
                       (print-term-tree term t))
                     ;; we mark 
                     (setq assoc-applied t)))))

          ;;  necesary to have true lowest parse

          (when (method-is-commutative head)
            (let* ((t1 (term$arg-1 body))
                   (t2 (term$arg-2 body))
                   (alt-op (lowest-method head
                                          (list (term-sort t2) (term-sort t1)))))
              (when (not (eq alt-op head))
                (term-replace term
                              (make-term-with-sort-check-bin alt-op (list t2 t1))))))
          (mark-term-as-lowest-parsed term)
          (values term assoc-applied))))))

;;; *********************************
;;; EQUALITY AMONG TERMS WITH/WITHOUT
;;; CONSIDERING EQUATIONAL THEORY    -------------------------------------------
;;; *********************************

;;; NOTE: compare term-head with eq is NOT dangerous.

(defmacro is-true? (!_obj)
  `(eq (term-head ,!_obj) *bool-true-meth*))
(defmacro is-false? (!_obj)
  `(eq (term-head ,!_obj) *bool-false-meth*))

;;; VARIABLE-EQUAL : VARIABLE VARIABLE -> BOOL
;;; returns true iff
;;; (1) two variables are phisically equal, or
;;; (2) have same name and same sort.
;;;
(defun variable-equal (x y)
  (declare (type term x y)
           (values (or null t)))
  (or (term-eq x y)
      (and (eq (variable-name x) (variable-name y))
           (sort= (variable-sort x) (variable-sort y)))))

(defun variable= (x y)
  (declare (type term x y)
           (values (or null t)))
  (term-eq x y))

(defun variable-eq (x y)
  (declare (type term x y)
           (values (or null t)))
  (term-eq x y))

;;; TERM-IS-ZERO-FOR-METHOD : TERM METHOD -> BOOL
;;; returns t if the term TERM is identity of method METHOD.
;;;
(defun term-is-zero-for-method (term meth)
  (declare (type term term)
           (type method meth)
           (values (or null t)))
  (let* ((th (method-theory meth))
         (zero (car (theory-zero th))))
    (declare (type op-theory th)
             (type (or null term) zero))
    (if zero ;; term
        (term-is-similar? term zero)
      nil)))

;;; TERM-OP-CONTAINS-THEORY
;;; returns t iff some op has equational theory
;;;
(defun term-op-contains-theory (term)
  (if (term-is-application-form? term)
      (let ((th (method-theory-info-for-matching (term-head term))))
        (or (not (theory-info-empty-for-matching th))
            (some  #'(lambda (sub) (term-op-contains-theory sub))
                   (term-subterms term))))
    nil))

;;; TERM-IS-CONGRUENT? : TERM TERM -> BOOL
;;; returns true if two term are in the same cogruent class.
;;; two terms are taken literally, and no equational theory is considered.
;;;
(defun term-is-congruent? (t1 t2)
  (declare (type term t1 t2)
           (values (or null t)))
  (let ((t1-body (term-body t1))
        (t2-body (term-body t2)))
    (cond ((term$is-variable? t1-body)
           (or (eq t1 t2)
               (and (term$is-variable? t2-body)
                    (eq (variable$name t1-body) (variable$name t2-body))
                    (sort= (variable$sort t1-body) (variable$sort t2-body)))))
          ((term$is-variable? t2-body) nil)
          ((term$is-application-form? t1-body)
           (and (term$is-application-form? t2-body)
                (if (method-is-same-qual-method (appl$head t1-body)
                                                (appl$head t2-body))
                    (let ((sl1 (appl$subterms t1-body))
                          (sl2 (appl$subterms t2-body)))
                      (loop (when (null sl1) (return (null sl2)))
                            (unless (term-is-congruent? (car sl1) (car sl2))
                              (return nil))
                            (setf sl1 (cdr sl1)
                                  sl2 (cdr sl2))))
                    nil)))
          ((term$is-builtin-constant? t1-body)
           (term$builtin-equal t1-body t2-body))
          ((term$is-builtin-constant? t2-body) nil)
          ((term$is-lisp-form? t1-body)
           (and (term$is-lisp-form? t2-body)
                (equal (term$lisp-function t1-body)
                       (term$lisp-function t2-body))))
          ((term$is-lisp-form? t2-body) nil)
          (t (break "Panic! unknown type of term to term-is-congruent?")))))

;;; TERM-EQUATIONAL-EQUAL : TERM TERM -> BOOL
;;; return t iff the two terms are equationally equal.
;;; t1,t2 both taken "literally",i.e. no normalization is preformed on terms.
;;;
(defvar *used==* nil)

(defun match-with-empty-theory (t1 t2)
  (declare (type term t1 t2)
           (values (or null t)))
  (or (term-eq t1 t2)
      (cond ((term-is-applform? t1)
             (unless (term-is-applform? t2)
               (setq *used==* t)
               (return-from match-with-empty-theory nil))
             ;;
             (let ((head1 (term-head t1))
                   (head2 (term-head t2))
                   (subs1 (term-subterms t1))
                   (subs2 (term-subterms t2)))
               (declare (type list subs1 subs2)
                        (type method head1 head2))
               (if (null subs1)
                   (and (null subs2)
                        (eq head1 head2))
                 (if (method-is-of-same-operator head1 head2)
                     (do* ((sub1 subs1 (cdr sub1))
                           (sub2 subs2 (cdr sub2))
                           (st1 nil)
                           (st2 nil))
                         ((null sub1) t)
                       (setq st1 (car sub1))
                       (setq st2 (car sub2))
                       (cond ((term-is-applform? st1)
                              (unless
                                  (and (term-is-applform? st2)
                                       (if (theory-info-empty-for-matching
                                            (method-theory-info-for-matching
                                             (term-head st1)))
                                           (match-with-empty-theory st1 st2)
                                         (term-equational-equal st1 st2)))
                                (return nil)))
                             ((term-is-variable? st1)
                              (setq *used==* t)
                              (unless (variable= st1 st2) (return nil)))
                             ((term-is-variable? st2)
                              (setq *used==* t)
                              (return nil))
                             ((term-is-builtin-constant? st1)
                              (unless (term-builtin-equal st1 st2) (return nil)))
                             (t
                              (break "Panic: unknown type of term"))))
                   nil))))
            ((term-is-builtin-constant? t1)
             (term-builtin-equal t1 t2))
            ((term-is-builtin-constant? t2) nil))))

(defun term-equational-equal (t1 t2)
  (declare (type term t1 t2)
           (values (or null t)))
  (or (term-eq t1 t2)
      (let ((t1-body (term-body t1))
            (t2-body (term-body t2)))
        (cond ((term$is-applform? t1-body)
               (let ((f1 (appl$head t1-body)))
                 (if (theory-info-empty-for-matching
                      (method-theory-info-for-matching f1))
                     (match-with-empty-theory t1 t2)
                   (E-equal-in-theory (method-theory f1) t1 t2))))
              ((term$is-builtin-constant? t1-body)
               (term$builtin-equal t1-body t2-body))
              ((term$is-builtin-constant? t2-body) nil)
              ((term$is-variable? t1-body)
               (setq *used==* t)
               (eq t1-body t2-body))
              ((term$is-variable? t2-body)
               (setq *used==* t)
               nil)
              ((term$is-lisp-form? t1-body)
               (and (term$is-lisp-form? t2-body)
                    (equal (term$lisp-code-original-form t1-body)
                           (term$lisp-code-original-form t2-body))))
              (t (break "term-equational-equal: not-implemented ~s" t1))))))

;;; TERM-IS-SIMILAR? : TERM TERM -> BOOL
;;; returns true iff two terms are similar, i.e., syntactically equal.
;;; (no consideration of equational theory).
;;;
(defun term-is-similar? (t1 t2)
  (declare (type term t1)
           (type (or term null) t2)
           (values (or null t)))
  (or (term-eq t1 t2)
      (if t2
          (let ((t1-body (term-body t1))
                (t2-body (term-body t2)))
            (cond ((term$is-application-form? t1-body)
                   (and (term$is-application-form? t2-body)
                        (if (method-w= (appl$head t1-body) (appl$head t2-body))
                            (let ((subs1 (term$subterms t1-body))
                                  (subs2 (term$subterms t2-body)))
                              (loop
                                ;; (when (null subs1) (return (null subs2)))
                                (when (null subs1) (return t))
                                (unless (term-is-similar? (car subs1) (car subs2))
                                 (return nil))
                               (setq subs1 (cdr subs1)  subs2 (cdr subs2))))
                            nil)))
                  ((term$is-variable? t1-body)
                   (and (term$is-variable? t2-body)
                        (sort= (variable$name t1-body)
                               (variable$name t2-body))))
                  ((term$is-variable? t2-body) nil)
                  ((term$is-builtin-constant? t1-body)
                   (term$builtin-equal t1-body t2-body))
                  ((term$is-builtin-constant? t2-body) nil)
                  ((term$is-lisp-form? t1-body)
                   (and (term$is-lisp-form? t2-body)
                        (equal (term$lisp-form-original-form t1-body)
                               (term$lisp-form-original-form t2-body))))
                  ((term$is-lisp-form? t2-body) nil)
                  (t (break "unknown type of term." )))))))

;;; ****************************
;;; APPLICATION FORM CONSTRUTORS
;;; with some additional works  ________________________________________________
;;; ****************************

;;; op make-term-check-op : method {subterms}list[term] -> term
;;;
(defun make-term-check-op (f subterms &optional module)
  (declare (type method f)
           (type list subterms)
           (type (or null module) module))
  (make-term-with-sort-check f subterms module))

;;; op make-term-check-op-with-sort-check :
;;;     operator {subterms}list[term] -> term
;;; check if f is a built-in-constant-op
;;;
(defun make-term-check-op-with-sort-check (f subterms &optional module)
  (declare (type method f)
           (type list subterms)
           (type (or null module) module)
           (values term))
  (make-term-with-sort-check f subterms module))

;;; MAKE-TERM-WITH-SORT-CHECK : METHOD SUBTERMS -> TERM
;;; construct application form from given method & subterms.
;;; the lowest method is searched and if found, construct a term with found
;;; method, otherwise, given method is used.
(defvar **sa-debug** nil)
(defun make-term-with-sort-check (meth subterms
                                  &optional (module (get-context-module)))
  (declare (type method meth)
           (type list subterms)
           (type module module))
  (let ((res nil))
    (if (do ((arl (method-arity meth) (cdr arl))
             (sl subterms (cdr sl)))
            ((null arl) t)
          (unless (sort= (car arl) (term-sort (car sl))) (return nil)))
        (setq res (make-applform (method-coarity meth) meth subterms))
      (let ((m (lowest-method meth
                              (mapcar #'(lambda (x) (term-sort x)) subterms) ;
                              module)))
        (setq res (make-applform (method-coarity m) m subterms))))
    (when **sa-debug**
      (format t "~%MTWSC: meth=")
      (print-chaos-object meth)
      (print "==> ")
      (term-print res)
      (format t ":")
      (print-chaos-object (term-head res))
      (force-output))
    res))

;;; MAKE-TERM-WITH-SORT-CHECK-BIN : METHOD SUBTERMS -> TERM
;;; same as make-term-with-sort-check, but specialized to binary operators.

(defun make-term-with-sort-check-bin (meth subterms
                                           &optional (module (get-context-module)))
  (declare (type method meth)
           (type list subterms)
           (type (or null module) module)
           (values term))
  (let ((s1 (term-sort (car subterms)))
        (s2 (term-sort (cadr subterms)))
        (res nil))
    (if (let ((ar (method-arity meth)))
          (and (sort= (car ar) s1)
               (sort= (cadr ar) s2)))
        (setq res (make-applform (method-coarity meth) meth subterms))
      (let ((lm (lowest-method meth (list s1 s2) module)))
        (setq res (make-applform (method-coarity lm) lm subterms))))
    (when **sa-debug**
      (format t "~&MTWSC-BIN: meth=")
      (print-chaos-object meth)
      (print "==> ")
      (term-print res)
      (format t ":")
      (print-chaos-object (term-head res))
      (force-output))
    res))


;;; ***************************************
;;; ACCESSORS & CONSTRUCTORS of APPLICATION
;;; FORM CONSIDERING EQUATIONAL THEORY     -------------------------------------
;;; ***************************************

;;; LIST-ASSOC-SUBTERMS : TERM METHOD -> List[Term]
;;; returns the flattened list of subterms of A (associative) operator.
;;; Ex. if f and g are A(ssociative), then
;;;     f(f(x,g(a,b)),f(a,h(c))) --> (x, g(a,b), a, h(c))
;;; * NOTE *
;;;TERM must be a application form with associative method METHOD as top.

#+GCL
(defun list-assoc-subterms (term method)
  (declare (type term term)
           (type method method)
           (values list))
  (let ((res (list-assoc-subterms-aux term method nil)))
    res))

(defun list-assoc-subterms-aux (term method lst)
  (declare (type term term)
           (type method method)
           (type list lst))
  (let ((body (term-body term)))
    (if (term$is-application-form? body)
        (progn
          (if (method-is-of-same-operator (appl$head body) method)
              (list-assoc-subterms-aux (term$arg-1 body) method
                                       (list-assoc-subterms-aux (term$arg-2 body)
                                                                method
                                                                lst))
              (cons term lst)))
        (cons term lst))))

#-GCL
(defun list-assoc-subterms (term method)
  (declare (type term term)
           (type method method)
           (values list))
  (labels ((list-a-subs (term method lst)
             (declare (type term term)
                      (type method method)
                      (type list lst)
                      (values list))
             (let ((body (term-body term)))
               (if (term$is-application-form? body)
                   (progn
                     (if (method-is-of-same-operator (appl$head body) method)
                         (list-a-subs (term$arg-1 body) method
                                      (list-a-subs (term$arg-2 body)
                                                   method
                                                   lst))
                         (cons term lst)))
                   (cons term lst)))))
    ;;
    (list-a-subs term method nil)))

;;; LIST-ASSOC-ID-SUBTERMS : TERM METHOD -> List[Term]
;;; returns the flattened list of subterms of AZ operator.
;;; * NOTE *
;;; TERM must be a application form with AZ method MEHTOD as top.

(defun list-assoc-id-subterms (term method)
  (declare (type term term)
           (type method method))
  (list-assoc-id-subterms-aux term method nil))

(defun list-assoc-id-subterms-aux (term method lst)
  (declare (type term term)
           (type method method)
           (type list lst))
  (let ((body (term-body term)))
    (if (term$is-variable? body)
        (cons term lst)
        (if (term-is-zero-for-method term method)
            lst
            (if (term$is-application-form? body)
                (if (method-is-of-same-operator (appl$head body) method)
                    (list-assoc-id-subterms-aux (term$arg-1 body)
                                                method
                                                (list-assoc-id-subterms-aux
                                                 (term$arg-2 body)
                                                 method
                                                 lst))
                    (cons term lst))
                (cons term lst))))))

#+:other
(defun list-assoc-id-subterms (term method)
  (declare (type term term)
           (type method method)
           (values list))
  (labels ((list-a-subs (term method lst)
             (declare (type term term)
                      (type method method)
                      (type list lst)
                      (values list))
             (let ((body (term-body term)))
               (if (term$is-variable? body)
                   (cons term lst)
                   (if (term-is-zero-for-method term method)
                       lst
                       (if (term$is-application-form? body)
                           (if (method-is-of-same-operator (appl$head body) method)
                               (list-a-subs (term$arg-1 body)
                                            method
                                            (list-a-subs
                                             (term$arg-2 body)
                                             method
                                             lst))
                               (cons term lst))
                           (cons term lst)))))))
    ;;
    (list-a-subs term method nil)))


;;; LIST-AC-SUBTERMS : TERM METHOD -> List[Term]
;;; returns the flattened list of subterms of AC (associative&commutative)
;;; operator. 
;;; * NOTE *
;;; TERM must be an application form with AC method METHOD as top.

#+GCL
(defun list-AC-subterms (term method)
  (declare (type term term)
           (type method method))
  (list-ac-subterms-aux term method nil))

(defun list-AC-subterms-aux (term method lst)
  (declare (type term term)
           (type method method)
           (type list lst))
  (let ((body (term-body term)))
    (if (term$is-application-form? body)
        (if (method-is-ac-restriction-of (appl$head body) method)
            (list-ac-subterms-aux (term$arg-1 body)
                                  method
                                  (list-ac-subterms-aux (term$arg-2 body)
                                                        method
                                                        lst))
            (cons term lst))
        (cons term lst))))

#-GCL
(defun list-AC-subterms (term method)
  (declare (type term term)
                      (type method method))
  (labels ((list-subs (term method lst)
             (declare (type term term)
                      (type method method)
                      (type list lst))
             (let ((body (term-body term)))
               (if (term$is-application-form? body)
                   (if (method-is-ac-restriction-of (appl$head body) method)
                       (list-subs (term$arg-1 body)
                                  method
                                  (list-subs (term$arg-2 body)
                                             method
                                             lst))
                       (cons term lst))
                   (cons term lst)))))
    ;;
    (list-subs term method nil)))

;;;
(defun gather-term-ac-leaf-ordered (term)
  (let ((subs (list-ac-subterms term (term-head term))))
    (with-in-module ((get-context-module))
      (sort subs #'(lambda (x y) (sort<= (term-sort x) (term-sort y) *current-sort-order*))))))

;;; LIST-ACZ-SUBTERMS term method -> list-of-temrs
;;; returns the flattened list of subterms of ACZ (associative&commutative with
;;; identity) operator.
;;; * NOTE *
;;; TERM must be an application form with ACZ method METHOD as top.

#+GCL
(defun list-ACZ-subterms (term meth)
  (declare (type term term)
           (type method meth))
  (list-ACZ-subterms-aux term meth nil))

(defun list-ACZ-subterms-aux (term method lst)
  (declare (type term term)
           (type method method)
           (type list lst))
  (let ((body (term-body term)))
    (if (term$is-variable? body)
        (cons term lst)
        (if (term-is-zero-for-method term method)
            lst
            (if (term$is-application-form? body)
                (if (method-is-ac-restriction-of (appl$head body) method)
                    ;; then the operator is binary of course
                    (list-ACZ-subterms-aux (term$arg-1 body)
                                           method
                                           (list-ACZ-subterms-aux
                                            (term$arg-2 body) method lst))
                    (cons term lst))
                (cons term lst))))))

#-GCL
(defun list-ACZ-subterms (term meth)
  (declare (type term term)
           (type method meth))
  (labels ((list-subs (term method lst)
             (declare (type term term)
                      (type method method)
                      (type list lst))
             (let ((body (term-body term)))
               (if (term$is-variable? body)
                   (cons term lst)
                 (if (term-is-zero-for-method term method)
                     lst
                   (if (term$is-application-form? body)
                       (if ;; (method-is-ac-restriction-of (appl$head body)
                           ;;                               method)
                           (method-is-of-same-operator (appl$head body)
                                                       method)
                           ;; then the operator is binary of course
                           (list-subs (term$arg-1 body)
                                      method
                                      (list-subs (term$arg-2 body)
                                                 method
                                                 lst))
                         (cons term lst))
                     (cons term lst)))))))
    ;;
    (list-subs term meth nil)))


;;; MAKE-RIGHT-ASSOC-NORMAL-FORM : method subterms -> term
;;; construct an application form term with subterms are organized in right
;;; associative way.
;;; * NOTE *
;;; METHOD must be righ-associative method.
;;;
(defun make-right-assoc-normal-form (meth subterms)
  (declare (type method meth)
           (type list subterms))
  ;;#||
  (when *term-debug*
    (format t "~&make-right-assoc-normal-form:")
    (format t "~& method = ")
    (print-chaos-object meth)
    (format t "~& subterms = ")
    (print-chaos-object subterms)
    (format t "~& length = ~d" (length subterms))
    (force-output))
  ;;||#
  (let ((res (if (= (length subterms) 2)
                 (make-applform (method-coarity meth) meth subterms)
               (make-applform (method-coarity meth)
                              meth
                              (list (car subterms)
                                    (make-right-assoc-normal-form meth (cdr subterms)))))))
    (when *term-debug*
      (format t "~& -- new term = ")(print-term-tree res) (force-output))
    res))

;;; MAKE-RIGHT-ASSOC-NORMAL-FORM-WITH-SORT-CHECK : method subterms -> term
;;; same as make-right-assoc-normal-form, but possibly assign lower sorts.
;;; * NOTE *
;;; METHOD must be righ-associative method.

(defun make-right-assoc-normal-form-with-sort-check (meth subterms)
  (declare (type method meth)
           (type list subterms)
           (values term))
  (if (= 1 (length subterms))
      (car subterms)
    (if (= 2 (length subterms))
        (make-term-with-sort-check-bin meth subterms)
      (make-term-with-sort-check-bin
       meth
       (list (car subterms)
             (make-right-assoc-normal-form-with-sort-check meth
                                                           (cdr subterms)))))))

;;; RIGHT-ASSOCIATIVE-NORMAL-FORM : TERM -> TERM
;;; Reconstruct the subterms to be right associative iff the head operator has
;;; associative theory.
;;; It is very important to realize that the associative normal
;;; form of a term must be a correct term in order to use the standard
;;; operations of replacement and "parcours". For example the associative 
;;; normal form of 1+((2+2)+1) must be (1+(2+(2+1))) and NOT (+ (1 2 2 1))
;;; which represent the associative class.

(defun right-associative-normal-form (t1)
  (declare (type term t1))
  ;; (format t "~&ranf: ")
  ;; (term-print t1)
  (let ((body (term-body t1)))
    (cond ((term$is-constant? body) t1)
          ((term$is-variable? body) t1)
          (t (let ((h-op (appl$head body)))
               (cond ((theory-contains-associativity (method-theory h-op))
                      (make-right-assoc-normal-form-with-sort-check
                       h-op 
                       (mapcar #'right-associative-normal-form 
                               (list-assoc-subterms t1 h-op))))
                     (t (make-applform (method-coarity h-op)
                                       h-op 
                                       (mapcar #'right-associative-normal-form 
                                               (term$subterms body))))))))))

;;; RIGHT-ASSOCIATIVE-ID-NORMAL-FORM : term -> term
;;; Reconstruct the subterms to be right associative considering identity, iff
;;; the head operator has associative theory with identity.
;;; * NOTE *
;;; head method must be associaitive method with identity.
(defun right-associative-id-normal-form (t1)
  (declare (type term t1))
  (if (term-is-applform? t1)
      (let ((meth (term-head t1)))
        (if (theory-contains-az (method-theory meth))
            (make-right-assoc-normal-form
             meth
             (mapcar #'right-associative-id-normal-form
                     (list-assoc-id-subterms t1 meth)))
          t1))
    t1))

;;; ID-NORMAL-FORM : term -> term
;;; returns the term simplified by considering identity theory among subterms.
;;;
(defun id-normal-form (t1)
  (declare (type term t1))
  (let ((body (term-body t1)))
    (cond ((term$is-constant? body) t1)
          ((term$is-variable? body) t1)
        (t (let ((meth (appl$head body)))
             (cond ((term-is-zero-for-method (term$arg-1 body) meth)
                    (id-normal-form (term$arg-2 body)))
                   ((term-is-zero-for-method (term$arg-2 body) meth)
                    (id-normal-form (term$arg-1 body)))
                   (t t1)))))))

;;; MAKE-RIGHT-ASSOC-ID-NORMAL-FORM : method subterms -> term
;;;
(defun make-right-assoc-id-normal-form (method subterms)
  (declare (type method method)
           (type list subterms)
           (values list))
  (make-right-assoc-normal-form method (filter-zero method subterms)))

(defun filter-zero (method subterms)
  (declare (type method method)
           (type list subterms))
  (when subterms
    (if (term-is-zero-for-method (car subterms) method)
        (filter-zero method (cdr subterms))
      (cons (car subterms)
            (filter-zero method (cdr subterms))))))


;;; **********
;;; TERM CPIER------------------------------------------------------------------
;;; **********

;;; TERM-COPY-AND-RETURNS-LIST-VARIABLES : term -> term List[variable]
;;;

(defun term-copy-and-returns-list-variables (term)
  (declare (type term term)
           (values term list))
  (multiple-value-bind (res list-new-var)
      (copy-list-term-using-list-var (list term) nil)
    (declare (type list res list-new-var))
    (values (car res) list-new-var)))

(defun copy-list-term-using-list-var (term-list list-new-var &key (test #'variable-eq))
  (declare (type list term-list list-new-var)
           (values list list))
  (let ((v-image nil)
        (list-copied-term nil))
    (values (mapcar #'(lambda (term)
                        (cond ((term-is-variable? term)
                               (if (setq v-image
                                     (cdr (assoc term list-new-var :test test)))
                                   v-image
                                 (let ((new-var (variable-copy term)))
                                   (declare (type term new-var))
                                   (setf list-new-var (acons term new-var list-new-var))
                                   new-var)))
                              ((term-is-builtin-constant? term) term)
                              ((term-is-lisp-form? term) term)
                              (t (multiple-value-setq (list-copied-term list-new-var)
                                   (copy-list-term-using-list-var (term-subterms term)
                                                                  list-new-var
                                                                  :test test))
                                 (make-applform (term-sort term)
                                                (term-head term)
                                                list-copied-term))))
                    term-list)
            list-new-var)))

;;; COPY-TERM-USING-VARIABLE : term List[variable] -> term
;;;
(defun copy-term-using-variable (term list-new-var &optional (test #'variable-eq))
  (declare (type term term)
           (type list list-new-var)
           (values term))
  (multiple-value-bind (res list-new-var-res)
      (copy-list-term-using-list-var (list term) list-new-var :test test)
    (declare (ignore list-new-var-res)
             (type list res))
    (car res)))

;;; *****************************
;;; CONSTRUCTORS OF NORMAL FORM
;;; CONSIDERING EQUATIONAL THEORY-----------------------------------------------
;;; *****************************

;;; THEORY-STANDARD-FORM : Term -> Term
;;; Compute the (empty)-normal form of the term "t" with respect to the axioms
;;; of the current theory. For example if the current theory is AC(+)Z(+,0) then
;;; it computes the normal form for the axioms x+0 -> x, 0+x -> x.
;;; May be modified if one adds a new theory. Be carefull with the  potential
;;; extensions. 
;;; *NOTE*
;;; TERM is supposed of the application form f(t1,...,tn).
;;;
(defun theory-standard-form (term)
  (declare (type term term))
  (let ((body (term-body term)))
    (if (term$is-application-form? body)
        (let* ((f (appl$head body))
               (subterms (mapcar #'theory-standard-form (term$subterms body)))
               (th (method-theory f))
               (theory-info  (theory-info th))
               (t1 nil)
               (t2 nil))
          (let ((val (cond ((theory-info-is-empty-for-matching theory-info)
                            (make-applform (method-coarity f) f subterms))

                           ;; case x+0 -> x, 0+x -> x
                           ((and (progn
                                   (setq t1 (car subterms) t2 (cadr subterms))
                                   (theory-zero th))
                                 (let ((zero (car (theory-zero th))))
                                   (cond ((term-is-similar? t1 zero) t2)
                                         ((term-is-similar? t2 zero) t1)))))
                           ;; case x+x -> x
                           ((or (theory-info-is-I theory-info)
                                (theory-info-is-CI theory-info))
                            (if (term-is-similar? t1 t2) t1))

                           ;; It is more complex in the next cases because of 
                           ;; the presence of non trivial extensions
                           ;; and of commutativity, so we refer to appropriate
                           ;; procedure 
                           ((theory-info-is-AI theory-info)
                            (A-idempotent-normal-form f t1 t2))

                           ((or (theory-info-is-ACI theory-info) 
                                (theory-info-is-ACIZ theory-info))
                            (AC-idempotent-normal-form f t1 t2))
                           )))
            (if val
                val
              (make-applform (method-coarity f) f subterms))))
      term)))

(defun A-idempotent-normal-form (f t1 t2)
  (declare (type method f)
           (type term t1 t2))
  (if (term-is-similar? t1 t2)
      t1
    (make-applform (method-coarity f) f (list t1 t2))))

(defun AC-idempotent-normal-form (f t1 t2)
  (declare (type method f)
           (type term t1 t2))
  (if (term-is-similar? t1 t2)
      t1
    (make-applform (method-coarity f) f (list t1 t2))))

;;; **********
;;; MISC UTILS------------------------------------------------------------------
;;; **********

(defun get-term-all-methods (term ans)
  (when (term-is-application-form? term)
    (pushnew (term-head term) (cdr ans) :test #'eq)
    (dolist (sub (term-subterms term))
      (get-term-all-methods sub ans))))

(defun term-heads (term)
  (declare (type term term))
  (let ((res (cons nil nil)))
    (get-term-all-methods term res)
    (cdr res)))

;;; synonym
(defmacro term-operators (term)
  `(term-heads ,term))

(defun clean-term (term)
  (declare (type term term))
  (if (term-is-application-form? term)
      (make-applform (method-coarity (term-head term))
                     (term-head term)
                     (mapcar #'clean-term (term-subterms term)))
    term))

(defun term-make-zero (method)
  (declare (type method method)
           (values (or null term)))
  (let ((zero (car (theory-zero (method-theory method)))))
    (if zero
        zero
        nil)))

;;; SUPPLY-PCONSTANTS
;;;
(defun supply-pconstants (term)
  (declare (type term term)
           (values term))
  (let ((target (simple-copy-term term)))
    (declare (type term target))
    (let ((vars (term-variables target)))
      (unless vars (return-from supply-pconstants term))
      (dolist (var vars target)
        (term-replace var
                      (make-pconst-term (variable-sort var)
                                        (variable-name var)
                                        (variable-print-name var)))))))

;;; *********************** 
;;; MISC PREDICATES ON TERM
;;; ***********************
(defun term-is-of-functional? (term)
  (if (term-is-applform? term)
      (not (method-is-behavioural (term-head term)))
      t))
          
(defun term-is-of-behavioural? (term)
  (if (term-is-applform? term)
      (method-is-behavioural (term-head term))
      nil))

(defun term-is-of-behavioural*? (term
                                 &optional (opinfo-table *current-opinfo-table*))
  (if (term-is-applform? term)
      (or (method-is-behavioural (term-head term))
          (method-is-coherent (term-head term) opinfo-table))
    nil))

(defun term-is-behavioural? (term)
  (declare (type term term)
           (values (or null t)))
  (and (sort-is-hidden (term-sort term))
       (or (term-is-constant? term)
           (let ((head (term-head term)))
             (or (method-is-behavioural head)
                 (method-is-coherent head))))))

(defun term-can-be-in-beh-axiom? (term)
  (declare (type term term)
           (values (or null t)))
  (cond ((term-is-applform? term)
         (if (eq (term-head term) *bool-if*)
             (and (term-can-be-in-beh-axiom? (term-arg-2 term))
                  (term-can-be-in-beh-axiom? (term-arg-3 term)))
           (and (if (find-if #'(lambda (x)
                                 (sort-is-hidden x))
                             (mapcar #'(lambda (y) (term-sort y))
                                     (term-subterms term)))
                    (or (method-is-behavioural (term-head term))
                        (method-is-coherent (term-head term)))
                  t)
                (every #'term-can-be-in-beh-axiom? (term-subterms term)))))
        (t t)))

(defun term-is-non-behavioural? (term)
  (declare (type term term)
           (values (or null t)))
  (not (term-is-behavioural? term)))

;;; returns t iff given term is a constructor, i.e.,
;;; the root is a constrctor operator, or it is a term of built-in sort.
;;;
(defun term-is-constructor? (term)
  (or (term-is-builtin-constant? term)
      (and (term-is-application-form? term)
           (method-is-constructor? (term-head term)))))

;;; we sometimes need to make variables on the fly.-----------------------------
;;; 
(let ((*var-num* 0))
  (declare (type fixnum *var-num*))
  (defun generate-variable (sort)
    (make-variable-term sort
                        (intern (format nil "#Genvar-~d" (incf *var-num*)))))
  (defun make-new-variable (name sort &optional (pname name))
    (make-variable-term sort
                        (intern (format nil "~a-~d" name (incf *var-num*)))
                        pname))
  (defun rename-variable (var)
    (make-variable-term (variable-sort var)
                        (intern (format nil "~a-~d"
                                        (variable-name var)
                                        (incf *var-num*)))))
  )

;;; inspecting term --- for debugging -----------------------------------------
;;;
(defun inspect-term (term &optional (occur nil) (context *current-module*))
  (flet ((print-occr ()
           (format t " ~A" (if (null occur) "top" (reverse occur)))))
    (with-in-module (context)
      (print-next)
      (format t "[NF=~a,LP=~a] "  (term-is-reduced? term) (term-is-lowest-parsed? term))
      (cond ((term-is-applform? term)
             (print-chaos-object (term-head term))
             (print-occr)
             (dotimes (x (length (term-subterms term)))
               (let ((*print-indent* (+ 2 *print-indent*)))
                 (inspect-term (term-arg-n term x) (cons (1+ x) occur)))))
            ((term-is-builtin-constant? term)
             (term-print-with-sort term)
             (print-occr))
            (t (print-chaos-object term)
               (print-occr))))))

;;;
;;; REPLACE-VARIABLES-WITH-TOC
;;;
(defun replace-variables-with-toc (term &optional (warn nil))
  (unless (term-is-applform? term)
    (return-from replace-variables-with-toc term))
  (let ((vars (term-variables term))
        (subst nil))
    (cond (vars
           (dolist (var vars)
             (unless (assoc var subst)
               (let ((toc (make-pconst-term
                           (variable-sort var)
                           (intern (concatenate 'string "`" (string (variable-name var)))))))
                 (push (cons var toc) subst))))
           (when (and warn (stringp warn))
             (with-output-chaos-warning ()
               (format t warn))
             (format t "~%substitution: ")
             (print-substitution subst))
           (multiple-value-bind (res list-new-var-res)
               (copy-list-term-using-list-var (list term) subst)
             (declare (ignore list-new-var-res))
             (car res)))
          (t term))))

;;; canonicalize-variables
;;;
(defun canonicalize-variables (list-term module)
  (with-in-module (module)
    (multiple-value-bind (list-copied-term list-new-var)
        (copy-list-term-using-list-var list-term nil :test #'variable-equal)
      (declare (ignore list-new-var))
      list-copied-term)))

;;; print-term-struct
;;;
(defun print-term-struct (term module &optional (stream *standard-output*))
  (with-in-module (module)
    (let ((*standard-output* stream))
      (print-next)
      (cond ((term-is-applform? term)
             (format t "~a" (method-name (term-head term)))
             (dotimes (x (length (term-subterms term)))
               (let ((*print-indent* (+ 2 *print-indent*)))
                 (print-term-struct (term-arg-n term x) module))))
            ((term-is-builtin-constant? term)
             (term-print term))
            (t (print-chaos-object term))))))

;;; EOF

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

;;;            *************************************
;;;            Utility functions on CLAUSE & LITERAL
;;;            *************************************

;;; IS-EQUALITY : term -> {:equal, :non-equal, :beh-equal}
;;; returns type of equality of the given term, nil if
;;; the root of the term is not equality.
;;;
(defun is-equality (term)
  (declare (type term))
  (and (term-is-application-form? term)
       (let ((head (term-head term)))
         (declare (type method head))
         (if (method-is-of-same-operator *fopl-eq* head)
             :equal
           (if (method-is-of-same-operator *bool-equal*
                                           head)
               :cafe-equal
             (if (method-is-of-same-operator *bool-nonequal*
                                             head)
                 :cafe-non-equal
               (if (method-is-of-same-operator *beh-equal*
                                               head)
                   :cafe-beh-equal
                 nil)))))))

;;; MARK-LITERAL : Literal -> Literal'
;;; set type of literal
;;;
(defun mark-literal (lit)
  (declare (type literal lit)
           (values t))
  (let* ((atom (literal-atom lit)))
    (cond ((eq *fopl-ans* (term-head atom))
           (setf (literal-type lit) :answer))
          (t (case (is-equality atom)
               (:equal (if (literal-sign lit)
                           (setf (literal-type lit) :pos-eq)
                         (setf (literal-type lit) :neg-eq)))
               (otherwise
                (setf (literal-type lit) :normal-atom))))
          )))

;;; COMPARE-LITERAL
;;; 1. positive > negative
;;; 2. answer > nonanswer
;;; 3. lexical ordering (see. compare term)
;;;
(defun compare-literal (l1 l2)
  (declare (type literal l1 l2))
  (if (and (positive-literal? l1)
           (negative-literal? l2))
      :greater
    (if (and (negative-literal? l1)
             (positive-literal? l2))
        :less
      (if (pn-flag propositional)
          (op-lex-precedence (term-head (literal-atom l1))
                             (term-head (literal-atom l2)))

        ;;
        (term-lex-order-vars (literal-atom l1)
                             (literal-atom l2)))
      )))

;;; LITERAL-EQUAL : Lteral1 Literal2 -> Bool
;;; 
(defun literal-equal (l1 l2)
  (declare (type literal l1 l2))
  (and (eq (literal-sign l1) (literal-sign l2))
       (term-is-similar? (literal-atom l1)
                         (literal-atom l2))))

;;; =================
;;; CLAUSE Data Base
;;; =================

;;; FIND-CLAUSE : ID Proof-system -> Clause
;;;
(defun find-clause (id psys)
  (declare (type (or fixnum symbol simple-string) id)
           (type psystem)
           (values list))
  (flet ((is-nat (tok)
           (and (stringp tok)
                (every #'digit-char-p tok))))
    (with-in-module ((psystem-module psys))
      (let ((clauses nil)
            (cl nil))
        (cond ((or (fixnump id) (is-nat id))
               (unless (fixnump id)
                 (setq id (read-from-string id)))
               (setq cl (get-clause id (psystem-clause-hash psys)))
               (unless cl
                 (with-output-chaos-error ('no-such-clause)
                   (format t "no such clause with Id ~d" id)))
               (push cl clauses))
              ((stringp id)
               (setq cl (get-bound-value id))
               (unless cl
                 (with-output-chaos-error ('unboud)
                   (format t "cound not find let variable ~a" id)))
               ;; find every clause derived from cl
               (maphash #'(lambda (key clause)
                            (declare (ignore key))
                            (if (term-eq cl (clause-formula clause))
                                (push clause clauses)))
                        (psystem-clause-hash psys)))
              ;;
              ((symbolp id)
               ;; axiom label
               (let ((axioms (get-all-rules-labelled *current-module* id)))
                 ;; find every clause derived from axioms
                 (dolist (ax axioms)
                   #||
                   (maphash #'(lambda (key clause)
                                (declare (ignore key))
                                (if (eq (clause-axiom clause)
                                        ax)
                                    (push clause clauses)))
                            (psystem-clause-hash psys))
                   ||#
                   (dolist (clause (psystem-axioms psys))
                     (when (eq (clause-axiom clause) ax)
                       (push clause clauses))))))
              ;;
              (t (with-output-chaos-error ('internal-error)
                   (format t "find-clause got illegual arg ~a" id))))
        clauses))))

;;; CLEAR-CLAUSE-HASH
;;; clean up clause hash table
;;;
(defun clear-clause-hash (psys)
  (declare (type psystem psys))
  (clrhash (psystem-clause-hash psys))
  (clrhash (psystem-demodulators psys)))

;;; DELETE-CLAUSE
;;;
(defun delete-clause (cl psys)
  (declare (type clause cl)
           (type psystem psys))
  (when (<= 0 (clause-id cl))
    (if .debug-pn-memory.
        (if   (remhash (clause-id cl) (psystem-clause-hash psys))
            (incf .pn-clause-deleted.)
          (with-output-chaos-warning ()
            (princ "deleting unregistered clause :")
            (print-next)
            (print-clause cl)))
      (remhash (clause-id cl) (psystem-clause-hash psys)))
    ))

(defun delete-clause! (cl-id psys)
  (declare (type fixnum cl-id)
           (type psystem psys)
           (values t))
  (when (<= 0 cl-id)
    (if .debug-pn-memory.
        (when (remhash cl-id (psystem-clause-hash psys))
          (incf .pn-clause-deleted.))
      (remhash cl-id (psystem-clause-hash psys)))
    ))

;;; CLAUSE CONSTRUCTOR
;;; ------------------

(defun new-clause (psys &optional formula)
  (declare (type psystem psys)
           (type (or null term) formula)
           (values clause))
  (let ((cl (make-clause :id (psystem-clause-counter psys))))
    (setf (gethash (clause-id cl) (psystem-clause-hash psys)) cl)
    (incf (psystem-clause-counter psys))
    (when formula
      (setf (clause-formula cl) formula))
    cl))

#||
(defun new-clause (psys &optional formula)
  (declare (ignore psys)
           (type (or null term) formula)
           (values clause))
  (let ((cl (make-clause)))
    ;; (setf (gethash (clause-id cl) (psystem-clause-hash psys)) cl)
    ;; (incf (psystem-clause-counter psys))
    (when formula
      (setf (clause-formula cl) formula))
    cl))

(defun register-clause (cl psys)
  (setf (clause-id cl) (psystem-clause-counter psys))
  (incf (psystem-clause-counter psys))
  (setf (gethash (clause-id cl) (psystem-clause-hash psys)) cl)
  cl)

||#

(defun reset-clause-db (psys)
  (declare (type psystem psys))
  (setf (psystem-clause-counter psys) 1)
  (clear-clause-hash psys)
  (setq .pn-clause-deleted. 0)
  (setq *sk-function-num* nil)
  (pn-reset-var-num)
  )

;;; COPY-CLAUSE
;;;
(defun copy-clause (cl &optional (psys *current-psys*)
                                 (literal-modifier nil))
  (declare (type clause cl)
           (type psystem psys)
           (type (or null (function (literal) literal))
                 literal-modifier)
           (values clause))
  (let ((new-vars-list nil)
        (vars nil)
        (lits nil)
        (new-clause nil))
    ;; gather variables
    (setq vars (clause-variables cl))

    ;; make new variables for each
    (setq new-vars-list (make-var-mapping vars))

    ;; make copy of literals
    (setq lits
      (mapcar #'(lambda (x)
                  (if literal-modifier
                      (funcall literal-modifier x)
                    (copy-literal x new-vars-list)))
              (clause-literals cl)))
    ;; make new clause
    (setq new-clause (new-clause psys (clause-formula cl)))
    (setf (clause-literals new-clause) lits)
    (dolist (l (clause-literals new-clause))
      (setf (literal-clause l) new-clause))
    ;;
    new-clause))

;;; MAKE-CLAUSE-SHALLOW-COPY
;;;
(defun make-clause-shallow-copy (cl &optional lits-to-be-deleted)
  (declare (type clause cl)
           (type list lits-to-be-deleted)
           (values clause))
  (let ((cl-new (make-clause :parents (clause-parents cl)
                             :id (clause-id cl)
                             :pick-weight (clause-pick-weight cl)
                             :attributes (clause-attributes cl)
                             :type (clause-type cl)
                             :bits (clause-bits cl)
                             :heat-level (clause-heat-level cl)
                             :formula (clause-formula cl))))
    (declare (type clause cl-new))
    (let ((lits nil))
      (declare (type list lits))
      (if lits-to-be-deleted
          (progn
            (dolist (lit (clause-literals cl))
              (declare (type literal lit))
              (unless (memq lit lits-to-be-deleted)
                (push lit lits)))
            (setq lits (nreverse lits)))
        (setq lits (clause-literals cl)))
      (setf (clause-literals cl-new) lits)
      cl-new)))

;;; MAKE-DUMMY-CLAUSE
;;;
(defun make-dummy-clause (cl lit)
  (declare (type clause cl)
           (type literal lit)
           (values clause literal fixnum))
  (let ((new-vars-list nil)
        (vars nil)
        (lits nil)
        (new-clause nil)
        (new-cl-id -1)
        (tlit nil))
    (declare (type list new-vars-list vars lits)
             (type (or null clause) new-clause)
             (type fixnum new-cl-id)
             (type (or null literal) tlit))
    ;; gather variables
    (setq vars (clause-variables cl))
    (unless vars
      (return-from make-dummy-clause
        (values cl lit new-cl-id)))
    ;; make new variables for each
    (setq new-vars-list (make-var-mapping vars))
    ;; make copy of literals
    (setq lits
      (mapcar #'(lambda (x)
                  (let ((nlit (copy-literal x new-vars-list)))
                    (when (eq x lit)
                      (setq tlit nlit))
                    nlit))
              (clause-literals cl)))
    ;; make new clause
    (setq new-clause (new-clause *current-psys* (clause-formula cl)))
    (setq new-cl-id (clause-id new-clause))
    (push (cons :dummy-clause new-cl-id) (clause-attributes new-clause))
    (setf (clause-literals new-clause) lits)
    (dolist (l (clause-literals new-clause))
      (setf (literal-clause l) new-clause))
    ;; 
    (setf (clause-id new-clause) (clause-id cl))
    (values new-clause tlit new-cl-id)
    ))


;;; =======================
;;; BASIC CLAUSE OPERATIONS
;;; =======================

;;; LITERAL-NUMBER : Literal -> Nat
;;; lit is which which (excluding answers) in the clause
;;; that contains it.
;;;
(defun literal-number (lit)
  (declare (type literal lit)
           (values fixnum))
  (let ((i 1))
    (declare (type fixnum i))
    (dolist (l (clause-literals (literal-clause lit)))
      (declare (type literal l))
      (when (eq lit l) (return))
      (unless (answer-literal? lit)
        (incf i)))
    i))

;;; ITH-LITERAL : Clause Nat -> Literal
;;; returns the i-th (non-answer) literal
;;;
(defun ith-literal (clause n)
  (declare (type clause clause)
           (type fixnum n)
           (values (or null literal)))
  (let ((i 0))
    (declare (type fixnum i))
    (dolist (lit (clause-literals clause))
      (declare (type literal lit))
      (unless (answer-literal? lit)
        (incf i))
      (when (= i n)
        (return-from ith-literal lit)))
    nil))

;;; CL-DELETE
(defun cl-delete (clause)
  (declare (type clause clause))
  (setf (clause-literals clause) nil)
  (setf (clause-attributes clause) nil)
  (setf (clause-parents clause) nil)
  (setf (clause-container clause) nil)
  (delete-clause clause *current-psys*))

(defun set-clause-container (list clause)
  (declare (type list list)
           (type clause clause)
           (values symbol))
  (if (eq list *usable*)
      (setf (clause-container clause) :usable)
    (if (eq list *sos*)
        (setf (clause-container clause) :sos)
      ;; TODO
      (setf (clause-container clause) :other)))
  )

;;; APPEND-CLAUSE : List Clause -> List'
;;;
(defun append-clause (list clause)
  (declare (type symbol list)
           (type clause clause)
           (values t))
  (case list
    (:sos
     (if *sos*
         (setf (cdr (last *sos*)) (cons clause nil))
       (setq *sos* (list clause)))
     (incf (pn-stat sos-size)))
    (:usable
     (if *usable*
         (setf (cdr (last *usable*)) (cons clause nil))
       (setq *usable* (list clause)))
     (incf (pn-stat usable-size)))
    (otherwise
     #||
     (with-output-panic-message-n (:p-gl-0010 (list 'append-clause list))
       ;; (format t "append-clause: not yet ~s" list)
       )
     ||#
     ))
  (setf (clause-container clause) list)
  )

;;; PREPEND-CLAUSE : List Clause -> List'
;;;
(defun prepend-clause (list clause)
  (declare (type symbol list)
           (type clause clause))
  (let ((real-list nil))
    (declare (type list real-list))
    (case list
      (:sos (setq real-list *sos*)
            (incf (pn-stat sos-size)))
      (:usable (setq real-list *usable*)
               (incf (pn-stat usable-size)))
      #||
      (:demodulators (setq real-list *demodulators*)
                     (incf (pn-stat demodulators-size)))
      ||#
      )
    #||
    (unless real-list
      (with-output-panic-message-n (:p-pn-0040)
        ;; (princ "prepend-clause: nil")
        ))
    ||#
    (setf (cdr real-list) (cons (car real-list) (cdr real-list)))
    (setf (car real-list) clause)
    (setf (clause-container clause) list)))

;;; INSERT-BEFORE-CLAUSE : List Clause Clause-new -> List'
;;;
(defun insert-before-clause (list c1 c-new)
  (declare (type symbol list)
           (type clause c1 c-new)
           (values t))
  (let ((l nil))
    (declare (type list l))
    (case list
      (:sos (setq l *sos*)
            (incf (pn-stat sos-size)))
      (:usable (setq l *usable*)
               (incf (pn-stat usable-size)))
      )
    (let ((l-sub (member c1 l :test #'eq)))
      (unless l-sub
        (with-output-panic-message ()
          (princ "insert-before-clause: given illegal key")))
      (setf (cdr l-sub) (cons (car l-sub) (cdr l-sub)))
      (setf (car l-sub) c-new)
      (setf (clause-container c-new) list))))

;;; INSERT-AFTER-CLAUSE : List Clause Clause-new -> List'
;;;
(defun insert-after-clause (list c1 c-new)
  (declare (type symbol list)
           (type clause c1 c-new)
           (values t))
  (let ((l nil))
    (declare (type list l))
    (case list
      (:sos (setq l *sos*)
            (incf (pn-stat sos-size)))
      (:usable (setq l *usable*)
               (incf (pn-stat usable-size)))
      #||
      (:demodulators (setq l *demodulators*)
                     (incf (pn-stat demodulators-size)))
      ||#
      )
    (let ((pos (position c1 l))
          (l-sub nil))
      (unless pos
        (with-output-panic-message ()
          (princ "insert-after-clause: given illegal key")))
      (setq l-sub (nthcdr (1+ pos) l))
      (if l-sub
          (progn
            (setf (cdr l-sub) (cons (car l-sub) (cdr l-sub)))
            (setf (car l-sub) c-new))
        (nconc l (list c-new)))
      (setf (clause-container c-new) list))))

(defun delete-from-list (list clause)
  (declare (type symbol list)
           (type clause clause)
           (values t))
  (case list
    (:sos
     (decf (pn-stat sos-size))
     (setq *sos* (delete clause *sos*)))
    (:usable
     (decf (pn-stat usable-size))
     (setq *usable* (delete clause *usable*)))
    #||
    (t (with-output-panic-message ()
         (format t "delete-from-list: failed. ~s" list)
         (print-next)
         (print-clause clause)
         (break)))
    ||#
    (t nil)
    )
  (setf (clause-container clause) nil)
  )

;;; CLAUSE-FULL-UN-INDEX
;;;
(defun clause-full-un-index (clause)
  (declare (type clause clause))
  (un-index-all-literals clause)
  (un-index-demodulator clause)
  (when (eq (clause-container clause) :usable)
    (un-index-clash-literals clause))
  (delete-from-list (clause-container clause) clause)
  )

(defun clause-full-un-index-slow (clause)
  (declare (type clause clause))
  (un-index-all-literals-slow clause)
  (un-index-demodulator clause)
  (when (eq (clause-container clause) :usable)
    (un-index-clash-literals-slow clause))
  (delete-from-list (clause-container clause) clause)
  )

;;; CLAUSE-ALL-PARENTS
;;;
(defun clause-all-parents (clause &optional (psys *current-psys*))
  (declare (type clause clause)
           (type psystem psys)
           (values list))
  (let ((parents nil)
        (clause-hash (psystem-clause-hash psys))
        (so-far nil))
    (labels ((get-parents (c)
               (let ((plist nil))
                 (dolist (pl (clause-parents c))
                   (dolist (pid pl)
                     (when (and (integerp pid)
                                (not (member pid so-far)))
                       (push pid so-far)
                       (let ((pc (get-clause pid
                                             clause-hash)))
                         (if pc
                             (pushnew pc plist)
                           (with-output-chaos-warning ()
                             (format t "clause ~a is missing, proof incomplete."
                                     pid)))
                         ))))
                 (setq parents (nconc parents plist))
                 (dolist (p plist)
                   (get-parents p)))))
      (get-parents clause)
      (delete-duplicates parents))))

;;; ORDERED-SUB-CLAUSE : C D -> Bool
;;; t iff each literal of C occurs in D.
;;; literals assumed to be ordered by compare-literal.
;;;
(defun ordered-sub-clause (c d)
  (declare (type clause c d))
  (let ((lt1s (clause-literals c))
        (lt2s (clause-literals d)))
    (declare (type list lt1s lt2s))
    (do ((l1 (car lt1s) (car lt1s))
         (l2 (car lt2s) (car lt2s)))
        ((or (null lt1s) (null lt2s)))
      (declare (type (or null literal) l1 l2))
      (let ((cmp (compare-literal l1 l2)))
        (declare (type symbol cmp))
        (case cmp
          (:same (setq lt1s (cdr lt1s))
                 (setq lt2s (cdr lt2s)))
          (:greater (setq lt2s (cdr lt2s)))
          (:less (setq lt2s nil))
          (otherwise
           (with-output-panic-message ()
             (format t "ordered-sub-clause: not total."))))))
    (null lt1s)))

;;; CLAUSE-EQUAL C1 C2 : -> Bool
;;;
(defun clause-equal (c1 c2)
  (and (clause-p c1) (clause-p c2)
       (let ((ll1 (clause-literals c1))
             (ll2 (clause-literals c2)))
         (declare (type list ll1 ll2))
         (and (= (the fixnum (length ll1))
                 (the fixnum (length ll2)))
              (every #'(lambda (x) (find x ll2 :test #'literal-equal))
                     ll1)))))

;;; SUB-CLAUSE? : C D -> Bool
;;; - t iff each literal of c occurs in d.
;;; - literals are not assumed to be ordered.
;;; - treats any answer literals as ordinaly literals.
;;;
(defun sub-clause (c d)
  (declare (type clause c d))
  (dolist (lit (clause-literals c))
    (declare (type literal lit))
    (let ((find? (find-if #'(lambda (x)
                              (and (eq (literal-sign lit)
                                       (literal-sign x))
                                   (term-is-identical (literal-atom lit)
                                                      (literal-atom x))))
                          (clause-literals d))))
      (unless find?
        (return-from sub-clause nil))))
  t)

;;; SORT-LITERALS : Clause -> Clause'
;;;
(defun sort-literals (c)
  (declare (type clause c)
           (values clause))
  (setf (clause-literals c)
    (sort (clause-literals c)
          #'(lambda (x y)
              (declare (type literal x y))
              ;; (not (eq (compare-literal x y) :less))
              (eq (compare-literal x y) :less))
          ))
  c)

;;; *********
;;; UTILITIES
;;; *********

;;; NEXT-CLAUSE-NUM
;;;
(defun next-clause-num (&optional (psys *current-psys*))
  (declare (type psystem psys)
           (values fixnum))
  (psystem-clause-counter psys))

(defmacro sos-last-clause ()
  `(car (last *sos*)))

;;;
;;; CLAUSE-IS-BUILTIN-DEMOD
;;;
(defvar .use-bi-axiom-as-demod. nil)

#||
(defun clause-is-builtin-demod (cl)
  (declare (type clause cl))
  (or (let ((axiom (clause-axiom cl)))
        (and axiom
             (let ((labels (axiom-labels axiom)))
               (memq :bdemod labels))))
      (and (unit-clause? cl)
           (let ((lit (car (clause-literals cl))))
             (declare (type literal lit))
             (and (positive-eq-literal? lit)
                  (let ((atom (literal-atom lit)))
                    (declare (type term atom))
                    (and (term-is-lisp-form? (term-arg-2 atom))
                         (if (sort= (term-sort (term-arg-1 atom))
                                    *bool-sort*)
                             (method-is-meta-demod (term-head (term-arg-1 atom)))
                           t)))
                  )))))
||#

(defun clause-is-builtin-demod (cl)
  (declare (type clause cl))
  (let ((axiom (clause-axiom cl)))
    (and axiom
         (or (let ((labels (axiom-labels axiom)))
               (member ":BDEMOD" labels :test #'equal))
             (and .use-bi-axiom-as-demod.
                  (let ((rhs (rule-rhs axiom)))
                    (term-is-lisp-form? rhs)))))))

;;; CLAUSE-AXIOM-DECLARED-AS-DEMODULATOR
;;; returns t iff the corresponding axiom of the clause
;;; is declared as demodulator.
;;; 
(defun clause-axiom-declared-as-demodulator (cl)
  (declare (type clause cl))
  (let ((ax (clause-axiom cl)))
    (and ax
         (let ((lab (axiom-labels ax)))
           #||
           (with-output-simple-msg ()
             (format t "label=~s" lab))
           ||#
           (and (or (memq '|:DEMOD| lab)
                    (member ":DEMOD" lab :test #'equal))
                (if (memq (axiom-type ax)
                          '(:pignose-axiom :pignose-goal))
                    (progn
                      (with-output-chaos-warning ()
                        (princ "axiom is invalid for demodulator.")
                        (print-next)
                        (print-chaos-object ax))
                      nil)
                  t))))))

;;; CL-UNIQUE-VARIABLES
;;;
(defun cl-unique-variables (clause)
  (declare (type clause clause))
  (if (and (unit-clause? clause)
           (eq-literal? (car (clause-literals clause)))
           (term-is-lisp-form?
            (term-arg-2 (literal-atom (car (clause-literals clause))))))
      clause
    (let ((vars (clause-variables clause))
          (subst nil))
      (declare (type list vars subst))
      (dolist (v vars)
        (declare (type term v))
        (push (cons v (pn-make-new-variable v))
              subst))
      (dolist (lit (clause-literals clause))
        ;; (replace-term-vars (literal-atom lit) subst))
        (setf (literal-atom lit)
          (apply-subst subst (literal-atom lit))))
      clause)))

;;; UNIT-DELETION : Clause -> Bool
;;; - perform unit deletion
;;; - delete any literals that are subsumed by a unit with opossite sign.
;;; - returns t if any deletions occur.
;;;
(defun unit-deletion (clause)
  (declare (type clause clause))
  (let ((lits-to-be-deleted nil)
        (units nil))
    (declare (type list lits-to-be-deleted units))
    (dolist (lit (clause-literals clause))
      (declare (type literal lit))
      (let ((is-db (if (positive-literal? lit)
                       *neg-literals*
                     *pos-literals*))
            (atom (literal-atom lit)))
        (declare (type hash-table is-db)
                 (type term atom))
        (let (;; (lit-entry (get-literal-entry-from-atom is-db atom))
              (lit-entry (is-fetch atom is-db))
              (found? nil))
          (declare (type list lit-entry))
          #||
          (when (and (negative-literal? lit)
                     *universal-symmetry*)
            (push (car (clause-literals *universal-symmetry*)) lit-entry))
          ||#
          (dolist (data lit-entry)
            (dolist (lit2 data)
              (let* (                   ; (lit2 (literal-entry-literal data))
                     (d (literal-clause lit2)))
                (declare (type literal lit2)
                         (type clause d))
                (when (= (the fixnum (num-literals d)) 1)
                  (multiple-value-bind (subst no-match e-match)
                                        ; (pn-match (literal-entry-atom data) atom)
                      (pn-match (literal-atom lit2) atom)
                    (declare (ignore subst e-match))
                    (unless no-match
                      ;; subsumes....
                      (setq found? t)
                      (push (clause-id d) units)
                      (incf (pn-stat unit-deletes))
                      (when (pn-flag debug-infer)
                        (with-output-simple-msg ()
                          (format t "*unit-del: ~d subsumes ~d"
                                  (clause-id d)
                                  (clause-id clause))))
                      (return nil)))))))
          (when found?
            ;; this literal should be deleted.
            (push lit lits-to-be-deleted))
          )))
    ;;
    (if lits-to-be-deleted
        (progn
          (when (pn-flag debug-infer)
            (with-output-simple-msg ()
              (format t "- delete literals ~{~s ~}" lits-to-be-deleted))
            )
          (setf (clause-literals clause)
            (set-difference (clause-literals clause)
                            lits-to-be-deleted))
          (setf (clause-parents clause)
            (nconc (clause-parents clause)
                   (list (cons :unit-del-rule (nreverse units)))))
          t)
      nil)))

;;; BACK-UNIT-DELETION : Clause Bool -> Bool
;;; assumes given clause is a unit clause.
;;;
(defun back-unit-deletion (clause input?)
  (declare (type clause clause))
  (let* ((c-lit (ith-literal clause 1))
         (c-atom (literal-atom c-lit))
         (db (if (positive-literal? c-lit)
                 *neg-literals*
               *pos-literals*))
         (source-list nil))
    (declare (type literal c-lit)
             (type term c-atom)
             (type hash-table db)
             (type symbol source-list))
    (let (;; (entry (get-literal-entry-from-atom db c-atom))
          (entry (is-fetch c-atom db))
          )
      (dolist (lit-ent entry)
        (dolist (lit lit-ent)
          (setq source-list (clause-container clause))
          (when source-list
            (multiple-value-bind (subst no-match e-match)
                (pn-match c-atom
                          (literal-atom lit)
                          nil)
              (declare (ignore e-match)
                       (type list subst))
              (unless no-match
                (let ((resolvent (build-bin-res c-lit
                                                lit
                                                subst)))
                  (declare (type clause resolvent))
                  (setf (clause-parents resolvent)
                    (nconc (clause-parents resolvent)
                           (list (list ':back-unit-del-rule))))
                  ;;
                  (when (eq source-list :usable)
                    (set-bit (clause-bits resolvent) scratch-bit)
                    (print-clause resolvent))
                  ;;
                  (pre-process resolvent input? :sos)
                  ))))))
      )))

;;; MERGE-CLAUSE : Clause -> Clause'
;;; - merge identical literals
;;;
(defun merge-clause (clause)
  (declare (type clause clause))
  (setf (clause-literals clause)
    (delete-duplicates (clause-literals clause)
                       :test #'(lambda (x y)
                                 (and 
                                  (eq (literal-sign x)
                                      (literal-sign y))
                                  (term-is-identical (literal-atom x)
                                                     (literal-atom y))))))
  clause)

;;; CL-TAUTOLOGY? : Clause -> Bool
;;; returns t iff clause is a tautology
;;;
(defun cl-tautology? (c)
  (declare (type clause c))
  (let ((taut nil))
    (do* ((literals (clause-literals c) (cdr literals))
          (l1 (car literals) (car literals))
          (rest (cdr literals) (cdr literals)))
        ((or (null literals) taut) taut)
      (declare (type list literals)
               (type (or null literal) l1)
               (type list rest))
      (let ((l1-atom (literal-atom l1)))
        (declare (type term l1-atom))
        (dolist (l2 rest)
          (declare (type literal l2))
          (setq taut
            (and (not (eq (literal-sign (the literal l1))
                          (literal-sign l2)))
                 (term-is-identical l1-atom
                                    (literal-atom l2))))
          (when taut (return)))))
    ;;
    taut))

;;; PROOF-WEIGHT : Clause -> Fixnum
;;; - returns the number of leaves, i.e., occurrences of input clauses.
;;;   in the proof tree.
;;;
(defun proof-weight (clause psys)
  (declare (type clause clause)
           (type psystem psys)
           (values fixnum))
  (let ((sum 0))
    (declare (type fixnum sum))
    (dolist (ips (clause-parents clause))
      (declare (type list ips))
      (dolist (ip ips)
        (declare (type fixnum ip))
        (let ((d (get-clause ip (psystem-clause-hash psys))))
          (declare (type (or null clause) d))
          (when d
            (setq sum (+ sum (proof-weight d psys)))))))
    (if (= 0 sum)
        1
      sum)))

;;; PROOF-LENGTH : CLAUSE -> NAT
;;;
(defun proof-length (clause)
  (declare (ignore clause))
  (with-output-simple-msg ()
    (format t "proof-length: NOT YET, returns 0."))
  0)

;;; RENAME-CLAUSE-VARIABLES
;;; renae the variables of ta clause.
;;; return nil if more than *CLAUSEMAX-VARIABLES* distinct variables.
;;;
(defun rename-clause-variables (clause)
  (declare (type clause clause))
  (let ((ok t))
    (let ((*cl-vars-so-far* nil))
      (declare (special *cl-vars-so-far*)
               (type list *cl-vars-so-far*))
      (dolist (lit (clause-literals clause))
        (declare (type literal lit))
        (unless (rename-variables-in-term (literal-atom lit))
          (setq ok nil))))
    ok))

;;; do we really need this?
;;;
(defun rename-variables-in-term (term)
  (declare (type term term)
           (values term))
  term)

;;; ------------ 
;;; FIND CLAUSES
;;; ------------
(defun list-name2-list (l)
  (declare (type symbol l)
           (values list))
  (case l
    (:sos *sos*)
    (:usable *usable*)
    (:demodulators *demodulators*)
    (otherwise nil)))

(defun find-lightest-clause (l &optional delete)
  (declare (type symbol l))
  (let ((list (list-name2-list l)))
    (declare (type list list))
    (if list
        (let* ((felt (car list))
               (wm (clause-pick-weight felt))
               (rl (list felt))
               (res nil))
          (declare (type fixnum wm))
          (dolist (c (cdr list))
            (let ((cwt (clause-pick-weight c)))
              (declare (type fixnum cwt))
              (if (< cwt wm)
                  (setq wm cwt
                        rl (list c))
                (if (= cwt wm)
                    (push c rl)))))
          (if (and (pn-flag randomize-sos)
                   (cdr rl))
              (let ((sel (random (length rl))))
                (declare (type fixnum sel))
                (setq res (nth sel rl))
                (when (pn-flag debug-sos)
                  (with-output-simple-msg ()
                    (princ "** given clause candidates"))
                  (dotimes (x (length rl))
                    (with-output-simple-msg ()
                      (format t "(#~d)" x)
                      (print-clause (nth x rl))
                      (print-next)))
                  (with-output-simple-msg ()
                    (format t "++ selected (~#d)" sel))))
            (setq res (car (nreverse rl))))
          (when (and res delete)
            (delete-from-list l res))
          ;;
          res)
      nil)))

;;; FIND-GIVEN-CLAUSE 
;;;
(defun find-given-clause (&optional delete)
  (let ((given-clause nil))
    (declare (type (or null clause) given-clause))
    (cond ((pn-flag sos-queue)
           (setq given-clause (pop *sos*)))
          ((pn-flag sos-stack)
           (setq given-clause (car (last *sos*)))
           (setq *sos* (nbutlast *sos*)))
          ((not (= (pn-parameter pick-given-ratio) -1))
           (if (= 0 (mod (pn-stat cl-given)
                         (1+ (pn-parameter pick-given-ratio))))
               (setq given-clause (pop *sos*))
             (setq given-clause (find-lightest-clause :sos delete))))
          (t (setq given-clause (find-lightest-clause :sos delete))))
    given-clause))

;;; EXTRACT-GIVEN-CLAUSE
;;;
(defun extract-given-clause ()
  (declare (values (or null clause)))
  (find-given-clause :delete))

;;; WEIGHT-CLAUSE
;;; - weight a clause
;;;
(defun weight-clause (clause)
  (declare (type clause clause)
           (values fixnum))
  (let ((neg-weight-val (pn-parameter neg-weight))
        (w 0))
    (declare (type fixnum w neg-weight-val))
    (dolist (lit (clause-literals clause))
      (declare (type literal lit))
      (incf w (the fixnum (term-weight (literal-atom lit))))
      (when (negative-literal? lit)
        (incf w neg-weight-val)))
    w))

;;; ================
;;; SUBSUMTION TESTS
;;; ================

;;; SUBSUME? : C D -> Bool
;;; non-nil iff clause C subsumes clause D, i.e,
;;; there exists a substitution sigma(C) <= D.
;;;
#||
(defun subsume? (c d &optional (factor? nil))
  (declare (type clause c d)
           (ignore factor?))
  ;; avoid compare itself.
  ;; (when (eq c d) (return-from subsume? nil))
  ;; if factoring, don't let long clauses subsume shorter ones.
  ;; (when (and factor?
  ;;  (> (num-literals c) (num-literals d)))
  ;;  (return-from subsume? nil))
  ;;
  (let ((c-literals (clause-literals c))
        (d-literals (clause-literals d))
        (new-subst nil)
        (subst nil)
        (no-match nil)
        (e-match nil))
    (declare (type list c-literals d-literals new-subst subst))
    (unless c-literals (return-from subsume? nil))
    (dolist (lit c-literals)
      (declare (type literal lit))
      (unless (answer-literal? lit)
        (let ((c-atom (literal-atom lit))
              (sign (literal-sign lit)))
          (declare (type term c-atom))
          (unless (find-if
                   #'(lambda (x)
                       (cond ((eq sign (literal-sign x))
                              (multiple-value-setq (new-subst no-match e-match)
                                (pn-match c-atom
                                          (literal-atom x)
                                          subst
                                          ))
                              (if (not no-match)
                                  (progn
                                    (setq subst new-subst)
                                    t)
                                nil))
                             ;;
                             (t nil)))
                   d-literals)
            (return-from subsume? nil)))))
    ;; every literal of c matches some literal of d
    ;; thus c subsumes d.
    (when (pn-flag debug-infer)
      (with-output-simple-msg ()
        (princ "*subsume?: ")
        (print-clause c)
        (print-next) (princ " => ")
        (print-next)
        (print-clause d)
        )
      )
    t))
||#

(defparameter .MAX-LITERALS. 100)
(defvar .map-array. (make-array .MAX-LITERALS.))

(defun map-rest (c d subst)
  (let* ((c-lits (clause-literals c))
         (c-lit (car c-lits))
         (subsumed nil)
         (i 0))
    (declare (type fixnum i))
    (setq c-lit (car c-lits))
    (loop
      (when (or (null c-lit)
                (not (aref .map-array. i)))
        (return nil))
      (setq c-lits (cdr c-lits))
      (setq c-lit (car c-lits))
      (incf i))
    (unless c-lit 
      ;; all literals of c mapped, so c subsumes d
      (return-from map-rest t))
    (if (answer-literal? c-lit)
        (progn
          (setf (svref .map-array. i) t)
          (setq subsumed (map-rest c d subst))
          (setf (svref .map-array. i) nil))
      (let ((c-atom (literal-atom c-lit)))
        (setf (aref .map-array. i) t)   ; mark as mapped
        (dolist (d-lit (clause-literals d))
          (let ((d-atom (literal-atom d-lit)))
            (when (eq (literal-sign c-lit) (literal-sign d-lit))
              (multiple-value-bind (new-subst no-match e-match)
                  (pn-match c-atom d-atom subst)
                (declare (ignore e-match))
                (unless no-match
                  (when (map-rest c d new-subst)
                    (setq subsumed t)
                    (return)))))))
        (setf (aref .map-array. i) nil))) ; unmark 
    ;;
    subsumed))

(defun subsume? (c d)
  (declare (type clause c d))
  (dotimes (x (num-literals c))
    (setf (svref .map-array. x) nil))
  (if (map-rest c d nil)
      (progn
        ;; every literal of c matches some literal of d
        ;; thus c subsumes d.
        (when (pn-flag debug-infer)
          (with-output-simple-msg ()
            (princ "*subsume?: ")
            (print-clause c)
            (print-next) (princ " => ")
            (print-next)
            (print-clause d)))
        t)
    nil))

;;; FORWARD-SUBSUME : Clause -> Clause
;;; attemps to find a clause that subsumes given clause.
;;;
(defun for-sub-prop (d)
  (declare (type clause d))
  (dolist (c *usable*)
    (declare (type clause c))
    (when (ordered-sub-clause c d)
      (return-from for-sub-prop c)))
  (dolist (c *sos*)
    (declare (type clause d))
    (when (ordered-sub-clause c d)
      (return-from for-sub-prop c)))
  nil)

#||
(defun forward-subsume (d)
  (declare (type clause d)
           (values (or null clause)))
  (when (pn-flag propositional)
    (return-from forward-subsume (for-sub-prop d)))
  (let ((factor? (pn-flag factor))
        (d-size 0)
        (c nil))                        ; result
    (declare (type fixnum d-size)
             (type (or null clause) c))
    ;; if factor, don't let long clauses subsume short.
    (when factor?
      (setq d-size (num-literals d)))
    ;;
    (let ((subsumed nil))
      (dolist (lit (clause-literals d))
        (declare (type literal lit))
        (when subsumed (return nil))
        (let ((db (if (positive-literal? lit)
                      *pos-literals*
                    *neg-literals*)))
          (declare (type hash-table db))
          (let* ((atom (literal-atom lit))
                 ;; (data (get-literal-entry-from-atom db atom))
                 (data (is-fetch atom db))
                 )
            (declare (type term atom))
            (dolist (cc data)
              (dolist (c-lit cc)
                (when subsumed (return nil))
                (let ((c-size 0))
                  (declare (type literal c-lit)
                           (type fixnum c-size))
                  (setq c (literal-clause c-lit))
                  (setq c-size (num-literals c))
                  (when (and (not (eq c d))
                             (= (literal-number c-lit) 1)
                             (or (not factor?)
                                 (<= c-size d-size)))
                    (setq subsumed (subsume? c d))))))
            #|| NOT YET
            (when (and subsumed
                       (pn-flag ancestor-subsume)) ; no flag ancestor-subsume now.
              (renumber-variables d)
              (setq subsumed (anc-subsume c d))
              (unless subsumed
                (incf (pn-stat cl-not-anc-subsumed)))
              )
            ||#
            )))
      ;;
      (if subsumed
          c
        nil))))
||#


(defun forward-subsume (d)
  (declare (type clause d)
           (values (or null clause)))
  (when (pn-flag propositional)
    (return-from forward-subsume (for-sub-prop d)))
  (let ((factor? (pn-flag factor))
        (d-size 0))
    (declare (type fixnum d-size))
    ;; if factor, don't let long clauses subsume short.
    (when factor?
      (setq d-size (num-literals d)))
    ;;
    (let ((subsumed nil))
      (setq subsumed 
        (block exit
          (dolist (lit (clause-literals d))
            (declare (type literal lit))
            (let ((db (if (positive-literal? lit)
                          *pos-literals*
                        *neg-literals*)))
              (let* ((atom (literal-atom lit))
                     (data (is-fetch atom db))
                     )
                (declare (type term atom))
                #||
                (dolist (cc data)
                  (dolist (c-lit cc)
                    (let ((c-size 0)
                          (c nil))
                      (declare (type literal c-lit)
                               (type fixnum c-size))
                      (setq c (literal-clause c-lit))
                      (setq c-size (num-literals c))
                      (when (and (not (eq c d))
                                 (or (not factor?)
                                     (<= c-size d-size)))
                        (when (subsume? c d)
                          (return-from exit c))))))
                ||#
                (foreach-dentry (c-lit data)
                                (let ((c-size 0)
                                      (c nil))
                                  (declare (type literal c-lit)
                                           (type fixnum c-size))
                                  (setq c (literal-clause c-lit))
                                  (setq c-size (num-literals c))
                                  (when (and (not (eq c d))
                                             (= (literal-number c-lit) 1)
                                             (or (not factor?)
                                                 (<= c-size d-size)))
                                    (when (subsume? c d)
                                      (return-from exit c)))))
                )))
          nil))
      subsumed)))

;;; BACK-SUBSUME : Clause -> List[Clause]
;;; returns the list of clauses subsumed by given clause.
;;;
(defun back-subsume (clause)
  (declare (type clause clause)
           (values list))
  (let ((factor? (pn-flag factor))
        (clause-size (num-literals clause))
        (db nil)
        (first-lit nil)
        (subsumed-clauses nil))
    (declare (type fixnum clause-size)
             (type (or null hash-table) db)
             (type (or null literal) first-lit)
             (type list subsumed-clauses))
    (dolist (lit (clause-literals clause))
      (declare (type literal lit))
      (unless (answer-literal? lit)
        (setq first-lit lit)
        (return)))
    (unless first-lit
      (with-output-chaos-warning ()
        (format t "back-subsume: called with empty clause ~S" clause)
        (return-from back-subsume nil)))
    ;;
    (if (positive-literal? first-lit)
        (setq db *pos-literals*)
      (setq db *neg-literals*))
    ;;
    (let ((list-clause (get-clashable-clauses-from-literal db first-lit t))
          (subsumed nil))
      (declare (type list list-clause))
      (dolist (d list-clause)
        (declare (type clause d))
        (when (and (not (eq clause d))
                   (or (not factor?)
                       (<= clause-size (num-literals d))))
          (setq subsumed (subsume? clause d))
          #|| no flag `ancestor-subsume' now.
          (when (and subsumed (pn-flag ancestor-subsume))
            (setq subsumed (ancestor-subsume clause d)))
          ||#
          (when subsumed
            (push d subsumed-clauses)))))
    ;;
    subsumed-clauses))

;;; UNIT-CONFLICT : Clause -> List[emptyClause]
;;; search for unit conflict, returns empty clause if found,
;;; otherwise nil.
;;; = assumption : given clause is a unit clause.
;;;
(defun unit-conflict (clause)
  (declare (type clause clause)
           (values list))
  (let ((lit (dolist (l (clause-literals clause))
               (unless (answer-literal? l)
                 (return l)))))
    (declare (type (or null literal) lit))
    (unless lit
      (with-output-panic-message ()
        (format t "unit-conflict: accepted empty clause!")))
    ;;
    (let* ((db (if (positive-literal? lit)
                   *neg-literals*
                 *pos-literals*))
           (atom (literal-atom lit))
                                        ; (clashes (get-literal-entry-from-atom db atom))
           (clashes (is-fetch atom db))
           (conflicts nil))
      (declare (type hash-table db)
               (type term atom)
               (type list clashes)
               (type list conflicts))
      ;;
      #||
      (when (and *universal-symmetry*
                 (negative-eq-literal? lit)
                 (unit-clause? clause))
        (push (car (clause-literals *universal-symmetry*)) clashes))
      ||#
      ;;
      (dolist (ent clashes)
        (dolist (lit2 ent)
          (let (                        ;(lit2 (literal-entry-literal ent))
                                        ; (atom2 (literal-entry-atom ent))
                (atom2 (literal-atom lit2))
                (sub nil))
            (declare (type literal lit2)
                     (type term atom2)
                     (type list sub))
            (unless (eq lit lit2)
              (when (= 1 (num-literals (the clause (literal-clause lit2))))
                (multiple-value-bind (new-subst no-match e-eq)
                    (unify atom atom2 sub)
                  (declare (ignore e-eq)
                           (type list new-subst))
                  (unless no-match
                    #||
                    (with-output-simple-msg ()
                      (format t "#unitconfliction:")
                      (print-next)
                      (format t " lit = ~s" lit)
                      ;; (print-clause (literal-clause lit))
                      (print-next)
                      (format t " lit2 = ~s" lit2))
                    ||#
                    (let ((e (build-bin-res lit lit2 new-subst)))
                      (declare (type clause e))
                      (merge-clause e)
                      (push e conflicts)
                      (incf (pn-stat empty-clauses))
                      (when (and (not (= -1 (pn-parameter max-proofs)))
                                 (<= (pn-parameter max-proofs)
                                     (pn-stat empty-clauses)))
                        (return))))))))))
      ;;
      conflicts)))

;;; ANCESTOR-SUBSUME : C D -> Bool
;;;    We already know that c subsumes d.  Check if d subsumes c and
;;;    ancestors(c) <= ancestors(d).
;;; NOT-USED YET
;;;
#||
(defun ancestor-subsume (c d)
  (if (subsume? d c)
      ;; followings are not implemented yet.
      (if (pn-flag PROOF-WEIGHT)
          (<= (proof-weight c *current-psys*) (proof-weight d *current-psys*))
        (<= (proof-length c) (proof-length d)))
    t))
||#

;;; PN-DISTINCT-CONSTANTS : Clause -> Clause
;;;
#||
(defun pn-distinct-constants (clause)
  (labels ((do-dconst (atom)
             (unless (term-is-application-form? atom)
               (return-from do-dconst nil))
             ;;
             (unless (method= (term-head atom) *fopl-eq*)
               (return-from do-dconst nil))
             (let ((lhs (term-arg-1 atom))
                   (rhs (term-arg-2 atom)))
               (if (and (term-is-application-form? lhs)
                        (null (term-subterms lhs))
                        (not (is-skolem (term-head lhs)))
                        (term-is-application-form? rhs)
                        (null (term-subterms rhs))
                        (not (is-skolem (term-head rhs))))
                   (if (term-is-identical lhs rhs)
                       (progn
                         ;; (term-replace atom *bool-true*)
                         :equal)
                     (progn
                       ;; (term-replace atom *bool-false*)
                       :non-equal))
                 nil))
             ))
    (dolist (lit (clause-literals clause))
      (let ((res (do-dconst (literal-atom lit))))
        (if (eq res :equal)
            (setf (literal-atom lit) *bool-true*
                  (literal-type lit) :normal-atom)
          (if (eq res :non-equal)
              (setf (literal-atom lit) *bool-false*
                    (literal-type lit) :normal-atom)))
        (when res
          (setf (clause-parents clause)
            (nconc (clause-parents clause)
                   (list (list :distinct-constants)))))))
    ))
||#

(defun pn-distinct-constants (clause)
  (labels ((do-dconst (atom lit)
             (unless (term-is-application-form? atom)
               (return-from do-dconst nil))
             ;; recurse on subterms.
             ;; #||
             (dolist (sub (term-subterms atom))
               (do-dconst sub lit))
             ;; ||#
             ;; 
             (unless (method= (term-head atom) *fopl-eq*)
               (return-from do-dconst nil))
             (let ((lhs (term-arg-1 atom))
                   (rhs (term-arg-2 atom)))
               (when (and (term-is-application-form? lhs)
                          (null (term-subterms lhs))
                          (not (is-skolem (term-head lhs)))
                          (term-is-application-form? rhs)
                          (null (term-subterms rhs))
                          (not (is-skolem (term-head rhs))))
                 (when (pn-flag debug-dist-const)
                   (with-output-simple-msg ()
                     (princ "** dist-const: ")
                     (print-clause clause)))
                 (if (term-is-identical lhs rhs)
                     (progn
                       (term-replace atom *bool-true*))
                   (progn (term-replace atom *bool-false*)))
                 (when (pn-flag debug-dist-const)
                   (with-output-simple-msg ()
                     (princ "==> ")
                     (print-clause clause)))
                 (setf (clause-parents clause)
                   (nconc (clause-parents clause)
                          (list (list :distinct-constants))))
                 t)
               )))
    (dolist (lit (clause-literals clause))
      (when (do-dconst (literal-atom lit) lit)
        (setf (literal-type lit) :normal-atom)))
    ))

;;; EOF

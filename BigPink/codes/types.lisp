;;;-*-Mode:LISP; Package: CHAOS; Base:10; Syntax:Common-lisp -*-
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
;;;
(in-package :chaos)
#|=============================================================================
                             System:Chaos
                            Module:BigPink
                           File:types.lisp
=============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;;                     *********************
;;;                     BASIC Data Structures
;;;                     *********************

#-(or draft-ansi-cl-2 ansi-cl :clisp)
;; (deftype boolean () '(or null (not null)))

;; #+:cmu
;; (deftype boolean () '(or null (not null)))

;;; =====
;;; QUEUE
;;; =====
;;; not used now.

;;; q -> (front-ptr . last-ptr)
;;;          |            |
;;;          V            V
;;;      (item1, ...., last-item)
;;;
(defun make-queue () (cons nil nil))

(defun list->queue (list)
  (cons list
        (last list)))

(defmacro queue-front-ptr (q)
  `(car ,q))

(defmacro queue-rear-ptr (q)
  `(cdr ,q))

(defmacro queue-set-front-ptr (q item)
  `(setf (car ,q) ,item))

(defmacro queue-set-rear-ptr (q item)
  `(setf (cdr ,q) ,item))

(defmacro empty-queue? (q)
  `(null (queue-front-ptr ,q)))

(defun queue-front (q)
  (if (empty-queue? q)
      nil
    (car (queue-front-ptr q))))

(defun queue-insert (q item)
  (let ((new-pair (cons item nil)))
    (cond ((empty-queue? q)
           (queue-set-front-ptr q new-pair)
           (queue-set-rear-ptr q new-pair)
           q)
          (t
           (setf (cdr (queue-rear-ptr q)) new-pair)
           (queue-set-rear-ptr q new-pair)
           q))))

(defun delete-queue (q)
  (cond ((empty-queue? q) nil)
        (t (queue-set-front-ptr q
                                (cdr (queue-front-ptr q))))))

;;; =======
;;; LITERAL 
;;; =======
(defstruct (literal (:print-function pr-literal) (:copier nil))
  (clause nil :type (or null clause))   ; containing clause
  (atom nil :type (or null term))       ; the body -- term
  (sign t :type symbol)                 ; nil if negation
  (type nil :type symbol)               ; :pos-eq, :neg-eq, :evaluable
                                        ; :conditional-demod
                                        ; :normal-atom
  (stat-bits 0 :type fixnum)            ; various bit flags
  )

;;; STAT-BITS
(defconstant scratch-bit #x01)
(defconstant oriented-eq-bit #x02)

(defmacro test-bit (x bit)
  `(not (= 0 (logand (the fixnum ,x) (the fixnum ,bit)))))

(defmacro set-bit (x y)
  `(setf ,x (logior ,x (the fixnum ,y))))

(defmacro clear-bit (x y)
  `(setf ,x (logand ,x (lognot (the fixnum ,y)))))


;;; types of non variable term containing in a literal.
;;; :term          : not an atom
;;; :normal-atom   : normal atom
;;; :pos-eq        : psitive equality atom
;;; :neg-eq        : negative equality atom
;;; :answer        : answer lieteral atom
;;; :lex-dep-demod : lex-dependent domodulator atom
;;; :evaluable     : evaluable term
;;; :conditional-demod : conditional demodulator

;;; POSITIVE-LITERAL?
;;;
(defmacro positive-literal? (_lit)
  `(literal-sign ,_lit))

(defmacro negative-literal? (_lit)
  `(null (literal-sign ,_lit)))

;;; ANSWER-LITERAL? : Literal -> Bool
;;; *NOT YET*
(defmacro answer-literal? (_lit)
  `(eq (literal-type ,_lit) :answer))

;;; POSITIVE-EQ-LITERAL? : Literal -> Bool
;;; returns no-nil iff literal is a positive equality literal.
;;;
(defmacro positive-eq-literal? (lit)
  `(eq :pos-eq (literal-type ,lit)))

;;; NEGATIVE-EQ-LITERAL? : Literal -> Bool
;;; returns no-nil iff literal is a negative equality literal
;;;
(defmacro negative-eq-literal? (lit)
  `(eq :neg-eq (literal-type ,lit)))

;;; EQ-LITERAL? : Literal -> Bool
;;; returns no-nil iff literal is an equality literal (pos or neg)
;;;
(defmacro eq-literal? (literal)
  (once-only (literal)
   `(or (positive-eq-literal? ,literal)
        (negative-eq-literal? ,literal))))

;;; PROPOSITIONAL-LITERAL?
;;;
(declaim (inline propositional-literal?))

(defun propositional-literal? (lit)
  (declare (type literal lit))
  (null (term-variables (literal-atom lit))))

;;; LITERAL PRINTER

#||
(defun pr-literal (lit stream &rest ignore)
  (declare (type literal lit)
           (type stream stream)
           (ignore ignore))
  (let ((.printed-vars-so-far. .printed-vars-so-far.))
    (unless (literal-sign lit)
      (princ "~(" stream)
      (setq .file-col. (1+ .file-col.)))
    (with-in-module ((get-context-module))
      (cond ((eq-literal? lit)
             (let* ((lhs (term-arg-1 (literal-atom lit)))
                    (rhs (term-arg-2 (literal-atom lit)))
                    (*print-indent* *print-indent*))
               (setq *print-indent* (max *print-indent*
                                          .file-col.))
               (setq .printed-vars-so-far.
                 (append .printed-vars-so-far.
                         (term-print lhs stream)))
               (setq .file-col. (file-column stream))
               (princ " = ")
               #||
               (if (print-check 0 30) ; 30?
                   (princ "= ")
                 (princ " = "))
               ||#
               (setq *print-indent*
                 (max *print-indent*
                      (setq .file-col. (file-column stream))))
               (setq .printed-vars-so-far.
                 (append .printed-vars-so-far.
                         (term-print rhs stream)))
               ))
            (t (setq .printed-vars-so-far.
                 (append .printed-vars-so-far.
                         (term-print (literal-atom lit) stream))))
            )
      )
    (unless (literal-sign lit)
      (princ ")" stream))
    .printed-vars-so-far.)
  )
||#

(defun pr-literal (lit stream &rest ignore)
  (declare (type literal lit)
           (type stream stream)
           (ignore ignore))
  (let ((.printed-vars-so-far. .printed-vars-so-far.))
    (unless (literal-sign lit)
      (princ "~(" stream)
      (setq .file-col. (1+ .file-col.)))
    (with-in-module ((get-context-module))
      (setq .printed-vars-so-far.
        (append .printed-vars-so-far.
                (term-print (literal-atom lit) stream))))
    (unless (literal-sign lit)
      (princ ")" stream))
    .printed-vars-so-far.))

;;; 
;;; some gobal flags
;;; t if our logic has two diffrent types of equality.
;; (declaim (type boolean *fopl-two-equalities*))
(defvar *fopl-two-equalities* nil)

;;; primitive built-in modules for supporting inference in FOPL
(defvar *fopl-sentence-module* nil)
(defvar *fopl-clause-form-module* nil)
;;; primitive sorts declared in the aboves.
(defvar *fopl-sentence-sort* nil)
(defvar *var-decl-list-sort* nil)
(defvar *fopl-clause-sort* nil)
(defvar *fopl-sentence-seq-sort* nil)
;;; primitive formula constructors
(defvar *var-decl-list* nil)
(defvar *fopl-and* nil)
(defvar *fopl-or* nil)
(defvar *fopl-imply* nil)
(defvar *fopl-iff* nil)
(defvar *fopl-neg* nil)
(defvar *fopl-forall* nil)
(defvar *fopl-exists* nil)
(defvar *fopl-eq* nil)
(defvar *fopl-beq* nil)
(defvar *fopl-ans* nil)

;;; not used 
(defvar *clause-constructor* nil)
(defvar *clause-constructor2* nil)
(defvar *fopl-sentence-seq* nil)
;;;

(declaim (inline term-is-atom?))
(defun term-is-atom? (term)
  (declare (type term term))
  (sort<= (term-sort term) *fopl-sentence-sort* *current-sort-order*))

;;; ======
;;; CLAUSE
;;; ======

(defstruct (clause (:print-function print-clause)
            ;; copier is defined in `clause.lisp'
            (:copier nil))
  (parents nil :type list)              ; parents produces this clause
  (literals nil :type list)             ; list of literal
  (id -1 :type fixnum)
  (pick-weight -1 :type fixnum)
  (attributes nil :type list)
  (type nil :type symbol)
  (bits 0 :type fixnum)
  (heat-level 0 :type fixnum)
  (formula nil :type (or null term))    ; original formula
  (axiom nil :type (or null axiom))     ; derived axiom if any.
  (container nil :type symbol)          ; containing list, one of
                                        ; :sos, :usable, :other...
  )

;;; GET-CLAUSE : id -> Clause
;;;
(defmacro get-clause (_id _hash)
  `(gethash ,_id ,_hash))

;;; types of members of clause's parent lists.
;;; positive integers are clause IDs.
;;;
;;; :BINARY-RES-RULE
;;; :HYPER-RES-RULE
;;; :NEG-HYPER-RES-RULE
;;; :UR-RES-RULE
;;; :PARA-INTO-RULE
;;; :PARA-FROM-RULE
;;; :LINKED-UR-RES-RULE
;;; :GEO-RULE
;;; :FACTOR-RULE
;;; :NEW-DEMOD-RULE
;;; :BACK-DEMOD-RULE
;;; :DEMOD-RULE
;;; :UNIT-DEL-RULE
;;; :EVAL-RULE
;;; :GEO-ID-RULE
;;; :FACTOR-SIMP-RULE
;;; :COPY-RULE
;;; :FLIP-EQ-RULE
;;; :CLAUSIFY-RULE
;;; :BACK-UNIT-DEL-RULE
;;; :SPLIT-RULE
;;; :SPLIT-NEG-RULE
;;; :LIST-RULE
;;; :DISTINCT-CONSTANTS
;;;
(defparameter cl-print-mergine 30)

(defun print-clause (cl &optional (stream *standard-output*) &rest ignore)
  (declare (type clause cl)
           (type stream stream)
           (ignore ignore))
  (let ((*print-pretty* nil)
        (.printed-vars-so-far. nil)
        (*print-xmode* :fancy)
        (*standard-output* stream)
        (fcol-1 0))
    #||
    (when (symbolp cl)
      (format stream "~a" cl)
      (return-from print-clause nil))
    ||#
    (let ((flg nil))
      (declare (type symbol flg))
      (when (<= 0 (clause-id cl))
        (format stream "~d:" (clause-id cl)))
      (setq fcol-1 (file-column stream))
      ;; (when (< 0 (clause-heat-level cl))
      ;;    (format t "(heat=~D) " (clause-heat-level cl)))
      (princ "[" stream)
      (dolist (ips (clause-parents cl))
        (declare (type list ips))
        (dolist (ip ips)
          (declare (type (or symbol fixnum list) ip))
          (if (eq flg :colon)
              (princ ":" stream)
            (if (eq flg :comma)
                (princ "," stream)))
          (cond ((symbolp ip)
                 (setq flg :colon)
                 (case ip
                   (:binary-res-rule (princ "binary" stream))
                   (:pbinary-res-rule (princ "prop-res" stream))
                   (:hyper-res-rule (princ "hyper" stream))
                   (:neg-hyper-res-rule (princ "neg-hyper" stream))
                   (:ur-res-rule (princ "ur" stream))
                   (:para-into-rule (princ "para-into" stream))
                   (:para-from-rule (princ "para-from" stream))
                   (:factor-rule (princ "factor" stream))
                   ;; (:factor-simp-rule (princ "factor-simp" stream))
                   (:factor-simp-rule (princ "fsimp" stream))
                   (:distinct-constants (princ "dconst" stream))
                   (:new-demod-rule (princ "new-demod" stream))
                   (:back-demod-rule (princ "back-demod" stream))
                   (:demod-rule (princ "demod" stream))
                   (:unit-del-rule (princ "unit-del" stream))
                   (:eval-rule (princ "eval" stream))
                   (:copy-rule (princ "copy" stream))
                   (:flip-eq-rule (princ "flip" stream))
                   (:back-unit-del-rule (princ "back-unit-del" stream))
                   (otherwise (princ ip stream))))
                ((atom ip)
                 (setq flg :comma)
                 (princ ip stream))
                ;; list
                (t (setq flg :comma)
                   (format stream "~a.~a" (car ip) (cdr ip)))))))
    ;;
    (princ "] " stream)
    (let* ((.file-col. (file-column stream))
           (flg nil)
           (*print-indent* *print-indent*)
           (ind-check 0))
      (declare (type symbol flg))
      (setq *print-indent* fcol-1)
      (if (print-check fcol-1 cl-print-mergine stream)
          (setq ind-check fcol-1)
        (setq ind-check .file-col.))
      (setq *print-indent* ind-check)
      (dolist (lit (clause-literals cl))
        (setq .file-col. (file-column stream))
        (if flg
            (progn 
              (princ " | " stream)
              (setq .file-col. (+ 3 .file-col.))
              (if (print-check ind-check 20 stream)
                  (setq .file-col. (file-column stream))
                )
              )
          (setq flg t))
        (setq .printed-vars-so-far.
          (append .printed-vars-so-far.
                  (pr-literal lit stream))))
      )))

#||
(defun print-clause (cl &optional (stream *standard-output*) &rest ignore)
  (declare (type clause cl)
           (type stream stream)
           (ignore ignore))
  (let ((*print-pretty* nil)
        (.printed-vars-so-far. nil)
        (*standard-output* stream)
        (fcol-1 0))
    (declare (special *print-pretty*))
    (let ((flg nil))
      (declare (type symbol flg))
      (format stream "~d:" (clause-id cl))
      (setq fcol-1 (file-column stream))
      ;; (when (< 0 (clause-heat-level cl))
      ;;    (format t "(heat=~D) " (clause-heat-level cl)))
      (princ "[" stream)
      (dolist (ips (clause-parents cl))
        (declare (type list ips))
        (dolist (ip ips)
          (declare (type (or symbol fixnum list) ip))
          (if (eq flg :colon)
              (princ ":" stream)
            (if (eq flg :comma)
                (princ "," stream)))
          (cond ((symbolp ip)
                 (setq flg :colon)
                 (case ip
                   (:binary-res-rule (princ "binary" stream))
                   (:pbinary-res-rule (princ "prop-res" stream))
                   (:hyper-res-rule (princ "hyper" stream))
                   (:neg-hyper-res-rule (princ "neg-hyper" stream))
                   (:ur-res-rule (princ "ur" stream))
                   (:para-into-rule (princ "para-into" stream))
                   (:para-from-rule (princ "para-from" stream))
                   (:factor-rule (princ "factor" stream))
                   ;; (:factor-simp-rule (princ "factor-simp" stream))
                   (:factor-simp-rule (princ "fsimp" stream))
                   (:distinct-constants (princ "dconst" stream))
                   (:new-demod-rule (princ "new-demod" stream))
                   (:back-demod-rule (princ "back-demod" stream))
                   (:demod-rule (princ "demod" stream))
                   (:unit-del-rule (princ "unit-del" stream))
                   (:eval-rule (princ "eval" stream))
                   (:copy-rule (princ "copy" stream))
                   (:flip-eq-rule (princ "flip" stream))
                   (:back-unit-del-rule (princ "back-unit-del" stream))
                   (otherwise (princ ip stream))))
                ((atom ip)
                 (setq flg :comma)
                 (princ ip stream))
                ;; list
                (t (setq flg :comma)
                   (format stream "~a.~a" (car ip) (cdr ip)))
                ))
        ))
    ;;
    (princ "] " stream)
    ))
||#

(defun pr-clause-list (cl &optional (detail nil))
  (declare (ignore detail)
           (type list cl))
  (dolist (c cl)
    (print-next)
    (print-clause c)
    ))

(defun print-clause-attributes (clause)
  (declare (type clause clause))
  (princ (clause-attributes clause)))

;;; CLAUSE-TO-TERM : Clause -> Term
;;; translate clause to term
;;;
(defun literals-to-term (lit-list)
  (declare (type list lit-list)
           (values term))
  (if (null lit-list)
      *bool-false*
    (let ((res nil))
      (declare (type (or null term) res))
      (do* ((lits lit-list (cdr lits))
            (l (car lits) (car lits)))
          ((null lits))
        (declare (type literal l))
        (if (literal-sign l)
            (push (make-term-with-sort-check
                   *fopl-neg*
                   (list (literal-atom l)))
                  res)
          (push (literal-atom l) res)))
      (if (cdr res)
          (setq res (make-right-assoc-normal-form-with-sort-check
                     *fopl-or*
                     (nreverse res)))
        (setq res (car res)))
      ;;
      res)))

(defun clause-to-term (cl)
  (declare (type clause cl)
           (values term))
  (literals-to-term (clause-literals cl)))

;;; LITERAL COPIER
;;;
(defun copy-literal (lit &optional variables clause subst)
  (declare (type literal lit)
           (type list variables subst)
           (type (or null clause) clause)
           (values literal))
  (let ((atom (literal-atom lit)))
    (declare (type term atom))
    (when subst
      (setq atom (apply-subst subst atom)))
    (make-literal :clause (if clause
                              clause
                            (literal-clause lit))
                  :atom (if variables
                            (copy-term-using-variable atom
                                                      variables)
                          (copy-term-reusing-variables atom
                                                      (term-variables atom)))
                  :sign (literal-sign lit)
                  :type (literal-type lit)))
  )

(defun shallow-copy-literal (lit &optional clause)
  (declare (type literal lit)
           (type (or null clause) clause)
           (values literal))
  (make-literal :clause (if clause
                            clause
                          (literal-clause lit))
                :atom (literal-atom lit)
                :sign (literal-sign lit)
                :type (literal-type lit)))


;;; CLAUSE-VARIABLES : Clause -> List[Variable]
;;;
(defun clause-variables (clause)
  (declare (type clause clause)
           (values list))
  (let ((vars nil))
    (declare (type list vars))
    (dolist (lit (clause-literals clause))
      (declare (type literal lit))
      (setq vars (nunion vars (term-variables (literal-atom lit))
                         :test #'!term-eq)))
    vars))

;;; CLAUSE-DISTINCT-VARIABLES (clause)
(declaim (inline clause-distinct-variables))

(defun clause-distinct-variables (clause)
  (declare (type clause clause)
           (values fixnum))
  (length (clause-variables clause)))

;;; GROUND-CLAUSE? : Clause -> Bool
;;;
(declaim (inline ground-clause?))
         
(defun ground-clause? (clause)
  (declare (type clause clause))
  (null (clause-variables clause)))

;;; NUM-LITERALS : Clause -> Nat
;;;
(declaim (inline num-literals))

(defun num-literals (clause)
  (declare (type clause clause)
           (values fixnum))
  (let ((num 0))
    (declare (type fixnum num))
    (dolist (lit (clause-literals clause))
      (declare (type literal lit))
      (unless (answer-literal? lit)
        (incf num)))
    num))

;;; NUM-ANSWERS : Clause -> Nat
;;;
(declaim (inline num-answers))

(defun num-answers (clause)
  (declare (type clause clause)
           (values fixnum))
  (let ((i 0))
    (declare (type fixnum i))
    (dolist (lit (clause-literals clause))
      (declare (type literal lit))
      (when (answer-literal? lit)
        (incf i)))
    i))

;;; NUM-LITERALS-ALL : Clause -> Nat
;;;
(declaim (inline num-literals-all))

(defun num-literals-all (clause)
  (declare (type clause clause)
           (values fixnum))
  (the fixnum (length (clause-literals clause))))

;;; UNIT-CLAUSE? : Clause -> Bool
;;; t if clause is a unit clause (exclude answer literals)
;;;
(declaim (inline unit-clause?))

(defun unit-clause? (clause)
  (declare (type clause clause))
  (= 1 (the fixnum (num-literals clause))))

;;; POSITIVE-CLAUSE? : Clause -> Bool
;;; returns t iff given clause is positive otherwise nil.
;;; (excludes answer literals.)
;;;
(declaim (inline positive-clause?))

(defun positive-clause? (clause)
  (declare (type clause clause))
  (every #'(lambda (lit)
             (declare (type literal lit))
             (or (positive-literal? lit)
                 (answer-literal? lit)))
         (clause-literals clause)))

;;; NEGATIVE-CLAUSE? : Clause -> Bool
;;;
(declaim (inline negative-clause?))

(defun negative-clause? (clause)
  (declare (type clause clause))
  (every #'(lambda (lit)
             (declare (type literal lit))
             (or (negative-literal? lit)
                 (answer-literal? lit)))
         (clause-literals clause)))

;;; PROPOSITIONAL-CLAUSE? : Clause -> Bool
;;; 
(declaim (inline propositional-clause?))

(defun propositional-clause? (clause)
  (declare (type clause clause))
  (every #'(lambda (lit)
             (declare (type literal lit))
             (let ((atom (literal-atom lit)))
               (and (not (term-is-variable? atom))
                    (term-is-constant? atom))))
         (clause-literals clause)))

;;; HORN-CLAUSE? : Clause -> Bool
;;; t if clause is a Horn Clause (at most one positive literal).
;;; (ignore answer literals).
;;;
(declaim (inline horn-clause?))

(defun horn-clause? (clause)
  (declare (type clause clause))
  (let ((i 0))
    (declare (type fixnum i))
    (dolist (lit (clause-literals clause))
      (declare (type literal lit))
      (when (and (positive-literal? lit)
                 (not (answer-literal? lit)))
        (incf i)))
    (<= i 1)))

;;; EQUALITY-CLAUSE? : Clause -> Bool
;;; t iff clause contains any equality literals (pos or neg).
;;;
(declaim (inline equality-clause?))

(defun equality-clause? (clause)
  (declare (type clause clause))
  (dolist (lit (clause-literals clause))
    (declare (type literal lit))
    (if (or (positive-eq-literal? lit)
            (negative-eq-literal? lit))
        (return-from equality-clause? t)))
  nil)

;;; SYMMETRY-CLAUSE? : Clause -> Bool
;;; t iff given clause is for symmetry of equality.
;;; i.e.,  X = Y  -> Y = X 
;;;       ~(X = Y) | Y = X
(defun symmetry-clause? (clause)
  (declare (type clause clause))
  (let ((lits (clause-literals clause)))
    (unless (= 2 (num-literals clause))
      (return-from symmetry-clause? nil))
    (let ((l1 (first lits))
          (l2 (second lits)))
      (declare (type literal l1 l2))
      (when (eq (literal-sign l1)
                (literal-sign l2))
        (return-from symmetry-clause? nil))
      (and (eq-literal? l1)
           (eq-literal? l2)
           (let ((t1 (literal-atom l1))
                 (t2 (literal-atom l2)))
             (and (term-is-variable? (term-arg-1 t1))
                  (variable-eq (term-arg-1 t1)
                               (term-arg-2 t2))
                  (term-is-variable? (term-arg-2 t1))
                  (variable-eq (term-arg-2 t1)
                               (term-arg-1 t2))))))))
               
;;; XX-RESOLVABLE : Clause -> Bool
;;; t if the non unit clause have a literal that can
;;; resolve with x = x.
;;;
(defun xx-resolvable (clause)
  (declare (type clause clause))
  (dolist (lit (clause-literals clause))
    (declare (type literal lit))
    (when (negative-eq-literal? lit)
      (let* ((atom (literal-atom lit))
             (a1 (term-arg-1 atom))
             (a2 (term-arg-2 atom)))
        (if (and (term-is-variable? a1)
                 (not (occurs-in a1 a2)))
            (return-from xx-resolvable t)
          (if (and (term-is-variable? a2)
                   (not (occurs-in a2 a1)))
              (return-from xx-resolvable t))))))
  nil)


;;; ============
;;; proof system
;;; ============
(defstruct psystem 
  (module nil)                          ; context module
  (sos nil)                             ; list of sos clause
  (usable nil)                          ; list of usable clause
  (passive nil)                         ; list of passive clause
  (axioms nil)                          ; list of axioms in clause form
  (demods nil)                          ; list of demod clauses
  (bi-demods nil)                       ; list of builtin demod clauses
  (clause-hash nil)                     ; hash table of clauses
  (demodulators nil)                    ; (make-hash-table :test #'eq))
                                        ; demodulator hash table
  (clause-counter 1)                    ; clause identifier counter
  )

(defun initialize-psystem (psys mod)
  (declare (type psystem psys)
           (type module mod)
           (values psystem))
  (setf (psystem-module psys) mod
        (psystem-sos psys) nil
        (psystem-usable psys) nil
        (psystem-axioms psys) nil
        (psystem-clause-counter psys) 1)
  (clrhash (psystem-clause-hash psys))
  (clrhash (psystem-demodulators psys))
  psys)

;;; CLASH
;;; used by hyper and UR resolution
;;; allocated one for each clashable literal of nucleus.
;;;
(defstruct (clash (:print-function print-clash))
  (literal nil :type (or null literal)) ; literal from nucleus
  (db nil :type (or null hash-table))   ; indexed table to use for
                                        ;  finding satellites
  (subst nil :type list)                ; unifying substitution
  (clashables nil :type list)
  (found-lit nil :type (or null literal)) ; unifying literal
  (evaluable nil)                       ; bi-demod
  (evaluation nil)                      ; ditto
  (already-evaluated nil)               ; ditto
  (prev nil :type (or null clash))      ; links
  (next nil :type (or null clash))
  )

(defun print-clash (obj &optional (stream *standard-output*)
                    &rest ignore)
  (declare (ignore ignore))
  (let* ((*standard-output* stream)
         (fcol (file-column stream))
         (*print-indent* (if (not (= 0 fcol))
                             fcol
                           (+ *print-indent* 4))))
    ;;
    (declare (type fixnum fcol *print-indent*))
    (do ((clash obj (clash-next clash))
         (num 0 (1+ num)))
        ((null clash))
      (declare (type fixnum num))
      (format t "#~d<clash: lit = " num)
      (prin1 (clash-literal clash))
      (print-next)
      (format t "clause-id = ~d" (clause-id (literal-clause
                                             (clash-literal clash))))
      (print-next)
      (princ "subst = ") (print-substitution (clash-subst clash))
      (print-next)
      (princ "found-lit = ") (prin1 (clash-found-lit clash))
      (print-next)
      (when (clash-found-lit clash)
        (format t "found clause-id = ~d"
                (clause-id (literal-clause (clash-found-lit clash)))))
      (when (clash-evaluable clash)
        (format t "evaluable: value = ~a" (clash-evaluation clash))
        (print-next)
        (format t "already evaled? = ~a" (clash-already-evaluated clash)))
      (princ ">")
      (print-next)
    )))

;;;
;;; PARAMODULATOR
;;;
(defstruct (paramod (:print-function pr-paramod))
  (lhs nil :type (or null term))
  (rhs nil :type (or null term))
  (literal nil :type (or null literal)))

(defun pr-paramod (obj &optional (stream *standard-output*) &rest ignore)
  (declare (ignore ignore))
  (let ((*standard-output* stream))
    (format t "#<paramod-rule: ")
    (term-print (paramod-lhs obj))
    (princ " = ")
    (term-print (paramod-rhs obj))
    (format t " (~D)>" (clause-id (literal-clause (paramod-literal obj))))
    ))

;;;
;;; DEMODULATOR
;;;
(defstruct (demod
            (:copier nil)
            (:constructor make-demod)
            (:print-function print-demodulator))
  (axiom nil :type (or null axiom))
  (order :normal :type symbol)
  (clause nil)
  )

(defmacro demod-lhs (_demod)
  `(axiom-lhs (demod-axiom ,_demod)))
(defmacro demod-rhs (_demod)
  `(axiom-rhs (demod-axiom ,_demod)))
(defmacro demod-condition (_demod)
  `(axiom-condition (demod-axiom ,_demod)))

(eval-when (:execute :load-toplevel)
  (setf (get 'demod :type-predicate) (symbol-function 'demod-p))
  (setf (get 'demod :print) 'print-demod-internal)
  (setf (symbol-function 'is-demod) (symbol-function 'demod-p))
  )

#||
(defun print-demod-object (obj &optional (stream *standard-output*) &rest ignore)
  (declare (ignore ignore))
  (format stream "#<demodulator (~a) ~a: ~x>"
          (clause-id (demod-clause obj))
          (demod-order obj) (addr-of obj)))
||#

(defun print-demodulator (demod &optional (stream *standard-output*) &rest ignore)
  (declare (ignore ignore))
  (let* ((lhs (demod-lhs demod))
         (rhs (demod-rhs demod))
         (clause (demod-clause demod))
         (clause-id (if (not (clause-p clause))
                        :*
                      (clause-id clause)))
         (.printed-vars-so-far. nil))
    (let ((*standard-output* stream)
          (.file-col. .file-col.)
          (indent 0))
      (format t "(~a) " clause-id)
      (setq indent (file-column stream))
      (setq .printed-vars-so-far.
        (term-print lhs))
      (setq .file-col. (file-column stream))
      (print-check indent .file-col.)
      (princ " --> ")
      (setq .file-col. (+ 5 .file-col.))
      (term-print rhs stream)
      (format stream " [~a]" (demod-order demod))
      )))

;;; ----------
;;; OPTION SET
;;; -----------
(defstruct (option-set)
  (name "" :type simple-string)
  (flags nil :type (or null simple-array))
  (parameters nil :type (or null simple-array))
  )

;;; EOF

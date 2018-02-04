;;;-*-Mode:LISP; Package: Chaos; Base:10; Syntax:Common-lisp -*-
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
#|==============================================================================
                                 System: Chaos
                           Module: primitives.chaos
                                File: term2.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;;**********
;;; TERM CELL
;;;*****************************************************************************
;;; <TERM> ::= <Variable> | <ApplForm > | <LispForm> | <PsuedoConstant>
;;;         |  <BuiltInConstant> | <SystemObject> ...
;;; * implementation
;;; <TERM> == ( . )
;;;             |
;;;             V
;;;         <BASE-TERM> 
;;;*****************************************************************************

;;; ============================================================================
;;; BASE-TERM : common 'term' body structure
;;; ============================================================================

(defstruct (base-term (:conc-name "TERM$") (:type list))
  (type 0 :type fixnum)                 ; variable, application form ...
  (status 0 :type fixnum)               ; lowest parsed, reduced ...
  (sort nil :type sort*))               ; sort of the term

(declaim (inline is-base-term-variant))
;;; should be enough for determining if an object is constructed from 'term-base'.
;;; used for determing an object is a term. the term itself is a cons containing a
;;; single 'term-base' object.
(defun is-base-term-variant (x)
  (and (consp x)                        ; it's a cons 
       (typep (car x) 'fixnum)          ; first element has type of fixnum
       (typep (cadr x) 'fixnum)         ; second element has status of fixnum
       (cdddr x)))                      ; and must have additional constructs
(deftype term-body ()
  `(satisfies is-base-term-variant))

;;; TERM-TYPE represents kind of a term
;;; #x001 : variable
;;; #x002 : application form 
;;; #x004 : simple lisp code
;;; #x008 : general lisp code
;;; #x00c : simple OR general lisp code
;;; #x010 : psuedo constant
;;; #x011 : variable treated as constant (variable AND psuedo constant)
;;; #x020 : pure builtin constant
;;; #x040 : system object
;;; $x070 : builtin constant (psuedo constant OR pure builtin OR system object)

(defconstant variable-type #x01)
(defconstant application-form-type #x02)
(defconstant simple-lisp-form-type #x04)
(defconstant general-lisp-form-type #x08)
;;; this type requires one of them is on
(defconstant lisp-form-type (logior simple-lisp-form-type general-lisp-form-type))
(defconstant psuedo-constant-type #x10)
(defconstant pure-builtin-constant-type #x20)
(defconstant system-object-type #x40)
;;; this type requires one of them is on
(defconstant builtin-constant-type (logior psuedo-constant-type
                                           pure-builtin-constant-type
                                           system-object-type))
;;; this type requires both flags are on
(defconstant constant-variable-type (logior variable-type
                                            psuedo-constant-type))

;;; TERM-STATUS
;;; represents states
;;; #x1000 : reduced flag       : on iff the term is reduced.
;;; #x2000 : lowest parsed flag : on iff the term is lowest parsed.
;;; #x4000 : on demand flag     : on iff the term is on deman.
;;; #x8000 : red flag           : on iff the term's context is not beh congruent.

(defconstant reduced-flag #x01)
(defconstant lowest-parsed-flag #x02)
(defconstant on-demand-flag #x04)
(defconstant red-flag #x08)

;;; ============================================================================
;;; TERM
;;; 'term' is a cell containing a variation of BASE-TERM
;;; ============================================================================

(defun is-term (obj)
  (and (consp obj)
       (typep (car obj) 'term-body)))

(deftype term () `(satisfies is-term))

;;; BASIC ACCESSORS
;;; ---------------

;;; TERM-BODY term -> BASE-TERM
(defmacro term-body (term) `(car ,term))

;;; TERM-CODE
;;;
(defmacro term-type (term) `(term$type (term-body ,term)))

;;; TERM-STATUS
;;;
(defmacro term-status (term) `(term$status (term-body ,term)))

;;; TERM-SORT
;;; ---------

;;; from term
(defmacro term-sort (*term) `(term$sort (term-body ,*term)))

;;; BASIC CONSTRUCTORS
;;; ------------------
(defmacro create-term (obj) `(list ,obj))

;;; make new term reusing existing term body
(defmacro new-term (_term) `(create-term (term-body ,_term)))

;;; PREDICATES
;;; ----------

;;; term-eq : term1 term2 -> bool
;;; returns t iff "term1" and "term2" are exactly the same object.
(defmacro term-eq (*t1 *t2) `(eq (term-body ,*t1) (term-body ,*t2)))

;;; term-equal : term1 term2 -> bool
;;; t iff "term1" and "term2" has the same representation.
(defmacro term-equal (*t1 *t2) `(equal ,*t1 ,*t2))

;;; type predicate 
;;; TERM? : object -> bool
(defmacro term? (object) 
  (once-only (object)
    `(and (consp ,object)
          (typep (car ,object) 'term-body))))

;;; TERM-REPLACE : from to -> from'
;;; term1 is modified so that its body becomes a body of term to.
;;;
(defmacro term-replace (from to) 
  `(setf (term-body ,from) (term-body ,to)))

;;; ============================================================================
;;; VARIANTS OF BASE-TERM
;;; ============================================================================

;;; --------
;;; VARIABLE
;;; --------
(defstruct (variable (:type list) (:conc-name "VARIABLE$")
            (:include base-term
                      (type variable-type)
                      ;; NOTE: variables are always 'reduced' and 'lowest parsed'
                      (status (logior reduced-flag lowest-parsed-flag))))
  (name nil)                            ; name 
  (print-name nil))                     ; name used for printing

;;; ---------------
;;; PSUEDO-CONSTNAT
;;; used for a temporal(on-the-fly) constant value in a constrained context
;;; ---------------
(defstruct (pconst (:type list) (:conc-name "PCONST$")
            (:include variable
                      (type psuedo-constant-type)
                      ;; NOTE: pconst is treated as 'lowest parsed' but not always 'reduced'
                      (status lowest-parsed-flag :type fixnum))))

;;; --------------------
;;; Operator APPLICATION
;;; --------------------
(defstruct (application (:type list) (:conc-name "APPL$")
            (:include base-term
                      (type application-form-type)))
  (head nil)                            ; operator
  (subterms nil :type list))            ; list of subterms

;;; ---------------------
;;; PURE Builtin CONSTANT
;;; ---------------------
(defstruct (pure-builtin (:type list) (:conc-name "BUILTIN$")
            (:include base-term
                      (type pure-builtin-constant-type)
                      ;; builtin constants are treated as 'reduced' and 'lowest parsed'
                      (status (logior reduced-flag lowest-parsed-flag))))
  (value nil)                           ; builtin value (a lisp object)
  )

;;; -------------
;;; SYSTEM OBJECT
;;; -------------
(defstruct (system-object (:type list) (:conc-name "SYSTEM$")
            (:include pure-builtin
                      (type system-object-type))))

;;; ----------------
;;; SIMPLE-LISP FORM
;;; ----------------
(defstruct (simple-lisp-form (:type list) (:conc-name "LISP-FORM$")
            (:include base-term
                      (type simple-lisp-form-type)
                      ;; simple-lisp-form is treated as 'reduced' and 'lowest parsed'
                      (status (logior reduced-flag lowest-parsed-flag))))
  (function nil)                        ;
  (original-form nil)                   ; the original lisp code
  )

;;; -----------------
;;; GENERAL-LISP FORM
;;; -----------------
(defstruct (general-lisp-form (:type list) 
            (:include simple-lisp-form
                      (type general-lisp-form-type))))

;;; --------------------
;;; TERM TYPE PREDICATES -------------------------------------------------------
;;; ============================================================================
(defmacro term-type-eq (?t1 ?t2)
  `(eq (term$type (term-body ,?t1))
       (term$type (term-body ,?t2))))

;;; TEST by accessing trm-body
(defmacro term$is-variable? (_term-body)
  `(eq variable-type (term$type ,_term-body)))
(defmacro term$is-application-form? (_term-body)
  `(eq application-form-type (term$type ,_term-body)))
(defmacro term$is-applform? (_term-body) ; synonym
  `(term$is-application-form? ,_term-body))
(defmacro term$is-simple-lisp-form? (_term-body)
  `(eq simple-lisp-form-type (term$type ,_term-body)))
(defmacro term$is-general-lisp-form? (_term-body)
  `(eq general-lisp-form-type (term$type ,_term-body)))
(defmacro term$is-lisp-form? (_term-body)
  `(test-and lisp-form-type (term$type ,_term-body)))
(defmacro term$is-pure-builtin-constant? (_term-body)
  `(eq pure-builtin-constant-type (term$type ,_term-body)))
(defmacro term$is-builtin-constant? (_term-body)
  `(test-and builtin-constant-type (term$type ,_term-body)))
(defmacro term$is-pconstant? (_term-body)
  `(eq psuedo-constant-type (term$type ,_term-body)))
(defmacro term$is-system-object? (_term-body)
  `(eq system-object-type (term$type ,_term-body)))
(defmacro term$is-constant-variable? (_term-body)
  `(eq constant-variable-type (term$type ,_term-body)))

;;; TEST via term cell
(defmacro term-is-variable? (_term)
  `(term$is-variable? (term-body ,_term)))
(defmacro term-is-application-form? (_term)
  `(term$is-application-form? (term-body ,_term)))
(defmacro term-is-applform? (_term)
  `(term$is-application-form? (term-body ,_term)))
(defmacro term-is-lisp-form? (_term)
  `(term$is-lisp-form? (term-body ,_term)))
(defmacro term-is-simple-lisp-form? (_term)
  `(term$is-simple-lisp-form? (term-body ,_term)))
(defmacro term-is-general-lisp-form? (_term)
  `(term$is-general-lisp-form? (term-body ,_term)))
(defmacro term-is-pure-builtin-constant? (_term)
  `(term$is-pure-builtin-constant? (term-body ,_term)))
(defmacro term-is-builtin-constant? (_term)
  `(term$is-builtin-constant? (term-body ,_term)))
(defmacro term-is-pconstant? (_term)
  `(term$is-pconstant? (term-body ,_term)))
(defmacro term-is-system-object? (_term)
  `(term$is-system-object? (term-body ,_term)))
(defmacro term-is-chaos-expr? (_term)
  `(and (term-is-builtin-constant? ,_term)
        (eq *chaos-value-sort* (term-sort ,_term))
        (let ((value (term-builtin-value ,_term)))
          (and (consp value)
               (eq (car value) '|%Chaos|)))))
(defmacro term-is-constant-variable? (_term)
  `(term$is-constant-variable? (term-body ,_term)))

;;; TERM-IS-CONSTANT? : term -> bool
;;; *note* we include variable-type and psuedo-constant-type for safety.
(defconstant priori-constant-type
  (logior variable-type lisp-form-type builtin-constant-type
          psuedo-constant-type
          system-object-type))

(defmacro term$is-constant? (_body)
  (once-only (_body)
    `(or (test-and priori-constant-type (term$type ,_body))
         (and (term$is-application-form? ,_body)
              (null (term$subterms ,_body))))))

(defmacro term-is-constant? (_term)
  `(term$is-constant? (term-body ,_term)))

;;; CHANGING treatment of vairables according to a situation.
;;; when we reduce a term with variables, we want treate them as if 
;;; they are constants.
;; mark variable as if its a constant
(defmacro mark-variable-as-constant (term)
  (once-only (term)
     `(and (term-is-variable? ,term)
           (setf (term-type ,term) constant-variable-type))))
(defmacro unmark-variable-as-constant (term)
  (once-only (term)
   `(and (term-is-constant-variable? ,term)
         (setf (term-type ,term) variable-type))))                   

;;; ----------------------
;;; TERM STATUS PREDICATES -----------------------------------------------------
;;; ============================================================================

(defmacro term$test-reduced-flag (term-body)
  `(test-and reduced-flag (term$status ,term-body)))

(defmacro term-is-reduced? (_term) 
  `(term$test-reduced-flag (term-body ,_term)))

;;; red flag
;;; --------
(defmacro term$test-red-flag (term-body)
  `(test-and red-flag (term$status ,term-body)))

(defmacro term-is-red (term)
  `(term$test-red-flag (term-body ,term)))

(defmacro term-is-green (term)
  `(zerop (logand red-flag (term$status (term-body ,term)))))

;;; lowest parsed flag
;;; ------------------

(defmacro term$test-lowest-parsed-flag (term-body)
  `(test-and lowest-parsed-flag (term$status ,term-body)))

(defmacro term-is-lowest-parsed? (_term)
  `(term$test-lowest-parsed-flag (term-body ,_term)))

;;; on demand flag
;;; --------------

(defmacro term$test-on-demand-flag (term-body)
  `(test-and on-demand-flag (term$status ,term-body)))

(defmacro term-is-on-demand? (_term)
  `(term$test-on-demand-flag (term-body ,_term)))

;;; --------------------
;;; TERM STATUS SETTERS --------------------------------------------------------
;;; ============================================================================

;;; reduced flag 
;;; -------------
(defmacro term$set-reduced-flag (term-body)
  (once-only (term-body)
    `(setf (term$status ,term-body)
           (make-or reduced-flag (term$status ,term-body)))))

(defmacro term-set-reduced-flag (term)
  `(term$set-reduced-flag (term-body ,term)))

(defmacro mark-term-as-reduced (_term)  ; synonym
  `(term-set-reduced-flag ,_term))

(defmacro term$unset-reduced-flag (term-body)
  (once-only (term-body)
     `(unless (zerop (logand reduced-flag (term$status ,term-body)))
        (setf (term$status ,term-body)
          (make-xor reduced-flag (term$status ,term-body))))))

(defmacro term-unset-reduced-flag (term)
  `(term$unset-reduced-flag (term-body ,term)))

(defmacro mark-term-as-not-reduced (_term) ; synonym
  `(term-unset-reduced-flag ,_term))

;;; red flag
;;; --------
(defmacro term$set-red-flag (term-body)
  (once-only (term-body)
     `(setf (term$status ,term-body)
        (make-or red-flag (term$status ,term-body)))))

(defmacro term-set-red (term)
  `(term$set-red-flag (term-body ,term)))

(defmacro term$set-green (term-body)
  (once-only (term-body)
     `(unless (zerop (logand red-flag (term$status ,term-body)))
        (setf (term$status ,term-body)
          (make-xor red-flag (term$status ,term-body))))))

(defmacro term-set-green (term)
  `(term$set-green (term-body ,term)))
  
;;; lowest parsed flag
;;; -------------------

(defmacro term$set-lowest-parsed-flag (term-body)
  (once-only (term-body)
    `(setf (term$status ,term-body)
           (make-or lowest-parsed-flag 
                    (term$status ,term-body)))))

(defmacro term-set-lowest-parsed-flag (term)
  `(term$set-lowest-parsed-flag (term-body ,term)))

(defmacro mark-term-as-lowest-parsed (_term)    ; synonym
  `(term-set-lowest-parsed-flag ,_term))

(defmacro term$unset-lowest-parsed-flag (term-body)
  (once-only (term-body)
    `(unless (zerop (logand lowest-parsed-flag (term$status ,term-body)))
       (setf (term$status ,term-body)
         (make-xor lowest-parsed-flag
                   (term$status ,term-body))))))

(defmacro term-unset-lowest-parsed-flag (term)
  `(term$unset-lowest-parsed-flag (term-body ,term)))

(defmacro mark-term-as-not-lowest-parsed (_term)        ; synonym
  `(term-unset-lowest-parsed-flag ,_term))

;;; on demand flag
;;; --------------

(defmacro term$set-on-demand-flag (term-body)
  (once-only (term-body)
   `(setf (term$status ,term-body)
          (make-or on-demand-flag
                   (term$status ,term-body)))))

(defmacro term-set-on-demand-flag (term)
  `(term$set-on-demand-flag (term-body ,term)))

(defmacro mark-term-as-on-demand (_term)        ; synonym
  `(term-set-on-demand-flag ,_term))

(defmacro term$unset-on-demand-flag (term-body)
  (once-only (term-body)
   `(unless (zerop (logand on-demand-flag (term$status ,term-body)))
      (setf (term$status ,term-body)
        (make-xor on-demand-flag
                  (term$status ,term-body))))))

(defmacro term-unset-on-demand-flag (term)
  `(term$unset-on-demand-flag ,term))

(defmacro mark-term-as-not-on-demand (_term) ; synonym
  `(term-unset-on-demand-flag ,_term))


;;; ----------------------------------------
;;; ACCESSORS of each term strucure variants --------------------------------
;;; =========================================================================

;;; -----------------
;;; APPLICATION FORM 
;;; -----------------
(defmacro term-head (_term) `(appl$head (term-body ,_term)))

(defmacro change$head-operator (_body _op)
  `(setf (appl$head ,_body) ,_op))

(defmacro change-head-operator (_term _op)
  `(change$head-operator (term-body ,_term) ,_op))

;;; subterms
;;; all of the followings are setf'able
(defmacro term$subterms (_term-body) `(appl$subterms ,_term-body))
(defmacro term$arg-1 (_term-body) `(car (appl$subterms ,_term-body)))
(defmacro term$arg-2 (_term-body) `(cadr (appl$subterms ,_term-body)))
(defmacro term$arg-3 (_term-body) `(caddr (appl$subterms ,_term-body)))
(defmacro term$arg-4 (_term-body) `(cadddr (appl$subterms ,_term-body)))
(defmacro term$arg-n (_term-body n)
  ` (the term
      (nth (the fixnum ,n) (appl$subterms ,_term-body))))
(defmacro term-subterms (_term)  `(appl$subterms (term-body ,_term)))
(defmacro term-arg-1 (_term) `(car (term-subterms ,_term)))
(defmacro term-arg-2 (_term) `(cadr (term-subterms ,_term)))
(defmacro term-arg-3 (_term) `(caddr (term-subterms ,_term)))
(defmacro term-arg-4 (_term) `(cadddr (term-subterms ,_term)))
(defmacro term-arg-n (_term n)
  ` (nth (the fixnum ,n)
         (term-subterms ,_term)))

;;; -------------
;;; VARIABLE TERM 
;;; -------------
(defmacro variable-sort (_term) `(term$sort (term-body ,_term)))
(defmacro variable-name (_term) `(variable$name (term-body ,_term)))
(defmacro variable-print-name (_term) `(variable$print-name (term-body ,_term)))

;;; --------------
;;; PCONSTANT TERM
;;; --------------
(defmacro pconst-sort (_term) `(term$sort (term-body ,_term)))
(defmacro pconst-name (_term) `(pconst$name (term-body ,_term)))
(defmacro pconst-print-name (_term) `(pconst$print-name (term-body ,_term)))

;;; ----------------
;;; BUILTIN CONSTANT
;;; ----------------
(defmacro term$builtin-value (_term-body) `(builtin$value ,_term-body))
(defmacro term-builtin-value (_term) `(term$builtin-value (term-body ,_term)))

;;; TERM-BUILTIN-EQUAL : term1 term2 -> bool
;;; assume term1 is builtin constant term
(defmacro term$builtin-equal (_builtin-body _term-body)
  (once-only (_term-body)
    `(and (term$is-builtin-constant? ,_term-body)
          (equal (term$builtin-value ,_builtin-body)
                 (term$builtin-value ,_term-body)))))

(defmacro term-builtin-equal (_bi-term _term)
  `(term$builtin-equal (term-body ,_bi-term) (term-body ,_term)))

;;; -----------
;;; CHAOS-VALUE
;;; -----------
(defmacro chaos-form-expr (_term)
  `(nth 1 (term-builtin-value ,_term)))
(defmacro chaos-original-expr (_term)
  `(nth 2 (term-builtin-value ,_term)))

;;; ---------------
;;; PSUEDO-CONSTANT
;;; ---------------
(defmacro term$psuedo-constant-name (_term-body) `(pconst$name ,_term-body))
(defmacro psuedo-constant-name (_term) `(term$psuedo-constant-name (term-body ,_term)))

;;; ---------
;;; LISP FORM
;;; ---------
(defmacro term$lisp-function (term-body) `(lisp-form$function ,term-body))
(defmacro term-lisp-function (term) `(term$lisp-function (term-body ,term)))
(defmacro lisp-form-function (term) `(term-lisp-function ,term)) ; synonym

(defmacro term$lisp-code-original-form (term-body)
  `(lisp-form$original-form ,term-body))
(defmacro term$lisp-form-original-form (term-body)
  `(term$lisp-code-original-form ,term-body)) ; synonym
(defmacro lisp-code-original-form (term)
  `(term$lisp-code-original-form (term-body ,term)))
(defmacro lisp-form-original-form (term)
  `(lisp-code-original-form ,term))     ; synonym

;;; -------------
;;; SYSTEM OBJECT
;;; -------------
(defmacro term$system-object (_term-body) `(system$value ,_term-body))
(defmacro term-system-object (_term) `(term$system-object (term-body ,_term)))


;;;*****************************************************************************
;;; TERM CONSTRUCTORS
;;;*****************************************************************************

;;; ********
;;; VARIABLE ___________________________________________________________________
;;; ********

;;; *NOTE* variables are always considered as reduced.
;;;        lowest parsed flag is also set to on.

(defconstant var-const-code
  (logior variable-type reduced-flag lowest-parsed-flag))

(declaim (inline make-variable-term))

(defun make-variable-term (sort variable-name &optional (print-name variable-name))
  (create-term (make-variable :sort sort :name variable-name :print-name print-name)))

(defmacro variable-copy (var)
  (once-only (var)
    `(make-variable-term (variable-sort ,var)
                         (variable-name ,var)
                         (variable-print-name ,var))))

;;; ****************
;;; APPLICATION-FORM ___________________________________________________________
;;; ****************
(declaim (inline make-application-term))

(defun make-application-term (op sort subterms)
  (create-term (make-application :head op :sort sort :subterms subterms)))

;;; ****************
;;; SIMPLE-LISP-CODE ___________________________________________________________
;;; ****************
(declaim (inline make-simple-lisp-form-term))

(defun make-simple-lisp-form-term (original-form)
  (create-term (make-simple-lisp-form :original-form original-form
                                      :sort *cosmos*)))

;;; *****************
;;; GENERAL-LISP-CODE __________________________________________________________
;;; *****************
(declaim (inline make-general-lisp-form-term))

(defun make-general-lisp-form-term (original-form)
  (create-term (make-general-lisp-form :original-form original-form
                                       :sort *cosmos*)))

;;; ****************
;;; BUILTIN CONSTANT ___________________________________________________________
;;; ****************
(declaim (inline make-bconst-term))

(defun make-bconst-term (sort value)
  (create-term (make-pure-builtin :value value :sort sort)))

;;; ***************
;;; PSUEDO CONSTANT____________________________________________________________
;;; ***************
(declaim (inline make-pconst-term))

(defun make-pconst-term (sort name &optional (print-name name))
  (create-term (make-pconst :sort sort :name name :print-name print-name)))

(defmacro pconst-copy (var)
  (once-only (var)
     `(make-pconst-term (pconst-sort ,var) 
                        (pconst-name ,var)
                        (pconst-print-name ,var))))

;;; *************
;;; SYSTEM OBJECT ____________________________________________________________
;;; *************
(declaim (inline make-system-object-term))

(defun make-system-object-term (value sort)
  (create-term (make-system-object :value value :sort sort)))

;;;*****************************************************************************
;;; BASIC UTILITIES
;;;*****************************************************************************

;;; TERM-VARIABLES : term -> LIST[variable]
;;;
(defun term-variables (term)
  (let ((body (term-body term)))
    (cond ((term$is-variable? body) (list term))
          ((term$is-constant? body) nil)
          (t (let ((res nil))
               (declare (type list res))
               (dolist (st (appl$subterms body) res)
                 (setq res (delete-duplicates (append res (term-variables st))
                                              :test #'(lambda (x y)
                                                        (term-eq x y))))))))))

(defun term-pvariables (term)
  (let ((body (term-body term)))
    (cond ((term$is-pconstant? body) (list term))
          ((or (term$is-constant? body) (term$is-variable? body)) nil)
          (t (let ((res nil))
               (declare (type list res))
               (dolist (st (appl$subterms body) res)
                 (setq res (delete-duplicates (append res (term-pvariables st))
                                              :test #'(lambda (x y)
                                                        (eq (variable-name x)
                                                            (variable-name y)))))))))))

(defun term-constant-variables (term)
  (let ((body (term-body term)))
    (cond ((term$is-constant-variable? body) (list term))
          ((term$is-constant? body) nil)
          (t (let ((res nil))
               (declare (type list res))
               (dolist (st (appl$subterms body) res)
                 (setq res (delete-duplicates (append res (term-constant-variables st))
                                              :test #'(lambda (x y)
                                                        (eq (variable-name x)
                                                            (variable-name y)))))))))))

(declaim (inline variables-occur-at-top?))

(defun variables-occur-at-top? (term)
  (block variables-occur-at-top-exit
    (dolist (st (term-subterms term))
      (when (term-is-variable? st)
        (return-from variables-occur-at-top-exit t)))))
  
;;; TERM-IS-GROUND? : term -> bool
;;;
(defmacro term$is-ground? (_body)
  (once-only (_body)
    `(block success
       (cond ((term$is-variable? ,_body) (return-from success nil))
             ((term$is-application-form? ,_body)
              (dolist (st (appl$subterms ,_body) t)
                (unless (term-is-ground? st)
                  (return-from success nil))))
             (t t)))))

(defun term-is-ground? (xx_term)
  (term$is-ground? (term-body xx_term)))

;;; SIMPLE-COPY-TERM : term -> new-term
;;; copies term.
;;; 
(declaim (inline simple-copy-term))
(defun simple-copy-term (term)
  (copy-tree (the list term)))

;;; EOF

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
(in-package :chaos)
#|=============================================================================
                                  System:CHAOS
                               Module: primitives
                              File: op-theory.lisp
=============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;;=============================================================================
;;;                             OPERATOR THEORY
;;;=============================================================================

;;; ***************
;;; OPERATOR THEORY_____________________________________________________________
;;; ***************
;;; An operator theory is associated to each method and with the following
;;; representation, a theory is, for example  [ACZ,(0)] which means that if this
;;; theory is associated to the operator "_+_" then the axioms related to "+"
;;; are x+(y+z) = (x+y)+z, x+y = y+x, x+0 = x, 0+x = x.
;;;
;;; The current theories supported are a combinaison of
;;; o associativity : x+(y+z) = (x+y)+z
;;; o commutativity : x+y = y+x
;;; o idempotence   : x+x = x     -- only partially implemented.
;;; o zero(identity): x+0 = x, 0+x = x
;;;
;;; Each of these is denoted by the following constant symbols encoding 8bit
;;; binary numbers.
;;;
;;; `.E.' : no axioms at all (empty theory)
;;; `.A.' : associativity
;;; `.C.' : commutativity
;;; `.Z.' : zero(identity)
;;; `.I.' : idempotence
;;;
;;; and their combinations:
;;;
;;;   .AC., .AI., .AZ., .CZ., .CI., .IZ.
;;;   .ACI., .ACZ., .CIZ., .AIZ.
;;;   .ACIZ.
;;;
;;;(defstruct (operator-theory
;;;             (:conc-name theory-)
;;;             (:print-function pr-optheory-internal)
;;;             (:constructor theory-make (info zero)))
;;;  info
;;;  zero)
(deftype op-theory () 'cons)

(defun theory-make (info zero)
  (cons info zero))

(defmacro theory-info (_th_) `(car ,_th_))
(defmacro theory-zero (_th_) `(cdr ,_th_))

(defun zero-rule-only (th)
  (declare (type op-theory th)
           (values (or null t)))
  (let ((val (theory-zero th)))
    (and val (cdr val))))

;;; ***********
;;; THEORY INFO_________________________________________________________________
;;; ***********

;;;(defstruct (theory-info
;;;             (:constructor new-theory-info
;;;                           (name code empty-for-unify
;;;                                 match-equal-fun match-init-fun match-next-fun
;;;                                 unify-equal-fun unify-init-fun unify-next-fun)))
;;;                           
;;;  name
;;;  code
;;;  empty-for-unify
;;;  match-equal-fun
;;;  match-init-fun
;;;  match-next-fun
;;;  unify-equal-fun
;;;  unify-init-fun
;;;  unify-next-fun)
#-GCL
(deftype theory-info () 'simple-vector)
#+GCL
(deftype theory-info () 'vector)

(defmacro theory-info-name (_th_)
  `(the symbol (svref ,_th_ 0)))
(defmacro theory-info-code (_th_)
  `(the fixnum (svref ,_th_ 1)))
(defmacro theory-info-empty-for-unify (_th_)
  `(the (or null t) (svref ,_th_ 2)))
(defmacro theory-info-empty-for-matching (_th_)
  `(the (or null t) (svref ,_th_ 2)))
(defmacro theory-info-match-equal-fun (_th_)
  `(the symbol (svref ,_th_ 3)))
(defmacro theory-info-match-init-fun (_th_)
  `(the symbol (svref ,_th_ 4)))
(defmacro theory-info-match-next-fun (_th_)
  `(the symbol (svref ,_th_ 5)))
(defmacro theory-info-unify-equal-fun (_th_)
  `(the symbol (svref ,_th_ 6)))
(defmacro theory-info-unify-init-fun (_th_)
  `(the symbol (svref ,_th_ 7)))
(defmacro theory-info-unify-next-fun (_th_)
  `(the symbol (svref ,_th_ 8)))

(defun new-theory-info (name code empty-for-unify match-equal-fun match-init-fun
                             match-next-fun unify-equal-fun unify-init-fun unify-next-fun)
  (declare (type symbol name match-equal-fun match-init-fun
                 match-next-fun unify-equal-fun unify-init-fun
                 unify-next-fun)
           (type (or null t) empty-for-unify)
           (type fixnum code)
           (values theory-info))
  (let ((th (alloc-svec 9)))
    (declare (type theory-info th))
    (setf (theory-info-name th) name)
    (setf (theory-info-code th) code)
    (setf (theory-info-empty-for-unify th) empty-for-unify
          (theory-info-match-equal-fun th) match-equal-fun
          (theory-info-match-init-fun th) match-init-fun
          (theory-info-match-next-fun th) match-next-fun
          (theory-info-unify-equal-fun th) unify-equal-fun
          (theory-info-unify-init-fun th) unify-init-fun
          (theory-info-unify-next-fun th) unify-next-fun)
    th))

(defun pr-theory-info (th-info)
  (format t "~%#<Theory ~s : init = ~s" 
          (theory-info-name th-info)
          (theory-info-match-init-fun th-info)))

(defun pr-optheory-internal (opth stream &rest ignore)
  (declare (ignore ignore))
  (format stream "#<Theory ~s : zero = ~s>"
          (theory-info-name (theory-info opth))
          (theory-zero opth)))

(defun is-operator-theory? (object)
  (declare (type t object)
           (values (or null t)))
  (and (consp object)
       (typep (car object) 'vector)
       (= 9 (length (the vector (car object))))))

;;; theory-info accessors via operator theory ---------------

(defmacro theory-name (_theory)
  `(theory-info-name (theory-info ,_theory)))
(defmacro theory-code (_theory)
  `(theory-info-code (theory-info ,_theory)))
(defmacro theory-empty-for-unify (_theory)
  `(theory-info-empty-for-unify (theory-info ,_theory)))
(defmacro theory-match-equal-fun (_theory)
  `(theory-info-match-equal-fun (theory-info ,_theory)))
(defmacro theory-match-init-fun (_theory)
  `(theor-info-match-init-fun (theory-info ,_theory)))
(defmacro theory-match-next-fun (_theory)
  `(theory-info-match-next-fun (theory-info ,_theory)))
(defmacro theory-unify-equal-fun (_theory)
  `(theory-info-unify-equal-fun (theory-info ,_theory)))
(defmacro theory-unify-init-fun (_theory)
  `(theory-info-unify-init-fun (theory-info ,_theory)))
(defmacro theory-unify-next-fun (_theory)
  `(theory-info-unify-next-fun (theory-info ,_theory)))

;;; Names of theories and their encoded number for each theory used for accessing
;;; theory informations. 
;;;
;;(declaim (special .E. .Z. .I. .C. .A. .AC. .AI. .AZ. .CZ. .CI. .IZ. .ACI.
;;                .ACZ. .CIZ. .AIZ. .ACIZ.))

(eval-when (:execute :compile-toplevel :load-toplevel)
  (defconstant .E. 0)
  (defconstant .Z. 1)
  (defconstant .I. 2)
  (defconstant .C. 4)
  (defconstant .A. 8)
  (defconstant .AC. (+ .A. .C.))
  (defconstant .AI. (+ .A. .I.))
  (defconstant .AZ. (+ .A. .Z.))
  (defconstant .CZ. (+ .C. .Z.))
  (defconstant .CI. (+ .C. .I.))
  (defconstant .IZ. (+ .I. .Z.))
  (defconstant .ACI. (+ .A. .C. .I.))
  (defconstant .ACZ. (+ .A. .C. .Z.))
  (defconstant .CIZ. (+ .C. .I. .Z.))
  (defconstant .AIZ. (+ .A. .I. .Z.))
  (defconstant .ACIZ. (+ .A. .C. .I. .Z.))
  )

;;; The bit tester for theories. multiple bits can be tested
#-gcl
(defmacro test-theory (_x _y)
  `(the (or null t)
    (not (= 0 (logand (the fixnum ,_x)
                      (the fixnum ,_y))))))
#+gcl
(defmacro test-theory (_x _y) `(test-and (the fixnum ,_x) (the fixnum ,_y)))
;;; 
(defmacro unset-theory (_x _y) `(logand ,_x (lognot ,_y)))

;;; ***************************
;;; BUILTIN THEORY INFORMATIONS_________________________________________________
;;; ***************************

;;; Each theory is created with the one of this infos.
;;;

#-GCL (declaim (type simple-vector *theory-info-array*))
#+GCL (declaim (type vector *theory-info-array*))
(defvar *theory-info-array* (alloc-svec 16))

(defmacro theory-code-to-info (_code)
  `(aref *theory-info-array* ,_code))

;;; CREATE-THEORY code-or-info zero
;;; creates a new instance of theory. 
;;; 
(defun create-theory (code-or-info zero)
  (declare (type (or fixnum theory-info) code-or-info)
           (type (or null t) zero)
           (values op-theory))
  (theory-make (if (numberp code-or-info)
                   (theory-code-to-info code-or-info)
                   code-or-info)
               zero))

(declaim (special the-e-property        ; .E.
                  the-z-property        ; .Z.
                  the-i-property        ; .I.
                  the-iz-property       ; .IZ.
                  the-c-property        ; .C.
                  the-cz-property       ; .CZ.
                  the-ci-property       ; .CI.
                  the-ciz-property      ; .CIZ.
                  the-a-property        ; .A.
                  the-az-property       ; .AZ.
                  the-ai-property       ; .AI.
                  the-ac-property       ; .AC.
                  the-acz-property      ; .ACZ.
                  the-aci-property      ; .ACI.
                  the-aiz-property      ; .AIZ.
                  the-aciz-property))   ; .ACIZ.

(defmacro define-theory-info (info-name
                              name
                              &key
                              empty-for-unify
                              match-equal-fun
                              match-init-fun
                              match-next-fun
                              unify-equal-fun
                              unify-init-fun
                              unify-next-fun)
  ` (eval-when (:execute :load-toplevel)
      (setf (aref *theory-info-array* ,name)
            (setf ,info-name
                  (new-theory-info ',name
                                   ,name
                                   ,empty-for-unify
                                   ',match-equal-fun
                                   ',match-init-fun
                                   ',match-next-fun
                                   ',unify-equal-fun
                                   ',unify-init-fun
                                   ',unify-next-fun)))))

(define-theory-info the-E-property .E.
  :empty-for-unify       t
  :match-equal-fun       match-empty-equal
  :match-init-fun        match-empty-state-initialize
  :match-next-fun        match-empty-next-state
  :unify-equal-fun       unify-empty-equal
  :unify-init-fun        unify-empty-state-initialize
  :unify-next-fun        unify-empty-next-state)

(define-theory-info the-Z-property .Z.
  :empty-for-unify       nil
  :match-equal-fun       match-z-equal
  :match-init-fun        match-z-state-initialize
  :match-next-fun        match-z-next-state
  :unify-equal-fun       unify-z-equal
  :unify-init-fun        unify-z-state-initialize
  :unify-next-fun        unify-z-next-state)

(define-theory-info the-I-property .I.
  :empty-for-unify       t
  :match-equal-fun       match-empty-equal
  :match-init-fun        match-empty-state-initialize
  :match-next-fun        match-empty-next-state
  :unify-equal-fun       unify-empty-equal
  :unify-init-fun        unify-empty-state-initialize
  :unify-next-fun        unify-empty-next-state)

(define-theory-info the-IZ-property .IZ.
  :empty-for-unify       nil
  :match-equal-fun       match-Z-equal
  :match-init-fun        match-Z-state-initialize
  :match-next-fun        match-Z-next-state
  :unify-equal-fun       unify-Z-equal
  :unify-init-fun        unify-Z-state-initialize
  :unify-next-fun        unify-Z-next-state)

(define-theory-info the-C-property .C.
  :empty-for-unify       nil
  :match-equal-fun       match-c-equal
  :match-init-fun        match-c-state-initialize
  :match-next-fun        match-c-next-state
  :unify-equal-fun       unify-c-equal
  :unify-init-fun        unify-c-state-initialize
  :unify-next-fun        unify-c-next-state)

(define-theory-info the-CZ-property .CZ.
  :empty-for-unify nil
  :match-equal-fun       match-cz-equal
  :match-init-fun        match-cz-state-initialize
  :match-next-fun        match-cz-next-state
  :unify-equal-fun       unify-cz-equal
  :unify-init-fun        unify-cz-state-initialize
  :unify-next-fun        unify-cz-next-state)

(define-theory-info the-CI-property .CI.
  :empty-for-unify       nil
  :match-equal-fun       match-c-equal
  :match-init-fun        match-c-state-initialize
  :match-next-fun        match-c-next-state
  :unify-equal-fun       unify-c-equal
  :unify-init-fun        unify-c-state-initialize
  :unify-next-fun        unify-c-next-state)

(define-theory-info the-CIZ-property .CIZ.
  :empty-for-unify       nil
  :match-equal-fun       match-cz-equal
  :match-init-fun        match-cz-state-initialize
  :match-next-fun        match-cz-next-state
  :unify-equal-fun       unify-cz-equal
  :unify-init-fun        unify-cz-state-initialize
  :unify-next-fun        unify-cz-next-state)

(define-theory-info the-A-property .A.
  :empty-for-unify       nil
  :match-equal-fun       match-A-equal
  :match-init-fun        match-A-state-initialize
  :match-next-fun        match-A-next-state
  :unify-equal-fun       unify-A-equal
  :unify-init-fun        unify-A-state-initialize
  :unify-next-fun        unify-A-next-state)

(define-theory-info the-AZ-property .AZ.
  :empty-for-unify nil
  :match-equal-fun       match-AZ-equal
  :match-init-fun        match-AZ-state-initialize
  :match-next-fun        match-AZ-next-state
  :unify-equal-fun       unify-AZ-equal
  :unify-init-fun        unify-AZ-state-initialize
  :unify-next-fun        unify-AZ-next-state)

(define-theory-info the-AI-property .AI.
  :empty-for-unify       nil
  :match-equal-fun       match-A-equal
  :match-init-fun        match-A-state-initialize
  :match-next-fun        match-A-next-state
  :unify-equal-fun       unify-A-equal
  :unify-init-fun        unify-A-state-initialize
  :unify-next-fun        unify-A-next-state)

(define-theory-info the-AIZ-property .AIZ.
  :empty-for-unify       nil
  :match-equal-fun       match-AZ-equal
  :match-init-fun        match-AZ-state-initialize
  :match-next-fun        match-AZ-next-state
  :unify-equal-fun       unify-AZ-equal
  :unify-init-fun        unify-AZ-state-initialize
  :unify-next-fun        unify-AZ-next-state)

(define-theory-info the-AC-property .AC.
  :empty-for-unify       nil
  :match-equal-fun       match-AC-equal
  :match-init-fun        match-AC-state-initialize
  :match-next-fun        match-AC-next-state
  :unify-equal-fun       unify-AC-equal
  :unify-init-fun        unify-AC-state-initialize
  :unify-next-fun        unify-AC-next-state)

(define-theory-info the-ACZ-property .ACZ.
  :empty-for-unify nil
  :match-equal-fun       match-ACZ-equal
  :match-init-fun        match-ACZ-state-initialize
  :match-next-fun        match-ACZ-next-state
  :unify-equal-fun       match-ACZ-equal
  :unify-init-fun        match-ACZ-state-initialize
  :unify-next-fun        match-ACZ-next-state)

(define-theory-info the-ACI-property .ACI.
  :empty-for-unify       nil
  :match-equal-fun       match-AC-equal
  :match-init-fun        match-AC-state-initialize
  :match-next-fun        match-AC-next-state
  :unify-equal-fun       unify-AC-equal
  :unify-init-fun        unify-AC-state-initialize
  :unify-next-fun        unify-AC-next-state)

(define-theory-info the-ACIZ-property .ACIZ.
  :empty-for-unify       nil
  :match-equal-fun       match-ACZ-equal
  :match-init-fun        match-ACZ-state-initialize
  :match-next-fun        match-ACZ-next-state
  :unify-equal-fun       unify-ACZ-equal
  :unify-init-fun        unify-ACZ-state-initialize
  :unify-next-fun        unify-ACZ-next-state)


;;; *THEORY-THE-EMPTY-THEORY*
(defvar *the-empty-theory*)
(eval-when (:execute :load-toplevel)
  (setf *the-empty-theory*
        (theory-make the-e-property nil)))

(defmacro theory-info-is-empty-for-unify (_theory-info)
  `(theory-info-empty-for-unify ,_theory-info))

(defmacro theory-info-is-empty-for-matching (_theory-info)
  `(theory-info-empty-for-unify ,_theory-info))

(defmacro theory-is-empty-for-unify (_theory)
  `(theory-info-empty-for-unify (theory-info ,_theory)))

(defmacro theory-is-empty-for-matching (_theory)
  `(theory-info-empty-for-unify (theory-info ,_theory)))

(defun theory-info-is-empty-for-unify-direct (theory-info)
  (or (eq the-e-property theory-info)
      (eq the-I-property theory-info)
      (eq the-Z-property theory-info)
      (eq the-IZ-property theory-info)))

(defmacro theory-info-is-empty (_theory-info)
  `(eq the-e-property ,_theory-info))
       
(defmacro theory-info-is-A (_theory-info)
  `(eq the-A-property ,_theory-info))

(defmacro theory-info-is-C (_theory-info)
  `(eq the-C-property ,_theory-info))

(defmacro theory-info-is-I (_theory-info)
  `(eq the-I-property ,_theory-info))

(defmacro theory-info-is-Z (_theory-info)
  `(eq the-Z-property ,_theory-info))

(defmacro theory-info-is-AC (_theory-info)
  `(eq the-AC-property ,_theory-info))

(defmacro theory-info-is-AI (_theory-info)
  `(eq the-AI-property ,_theory-info))

(defmacro theory-info-is-AZ (_theory-info)
  `(eq the-AZ-property ,_theory-info))

(defmacro theory-info-is-CI (_theory-info)
  `(eq the-CI-property ,_theory-info))

(defmacro theory-info-is-CZ (_theory-info)
  `(eq the-CZ-property ,_theory-info))

(defmacro theory-info-is-IZ (_theory-info)
  `(eq the-IZ-property ,_theory-info))

(defmacro theory-info-is-ACI (_theory-info)
  `(eq the-ACI-property ,_theory-info))

(defmacro theory-info-is-ACZ (_theory-info)
  `(eq the-ACZ-property ,_theory-info))

(defmacro theory-info-is-AIZ (_theory-info)
  `(eq the-AIZ-property ,_theory-info))

(defmacro theory-info-is-CIZ (_theory-info)
  `(eq the-CIZ-property ,_theory-info))

(defmacro theory-info-is-ACIZ (_theory-info)
  `(eq the-ACIZ-property ,_theory-info))

(defun theory-info-is-restriction-of (thn1 thn2)
  (= 0 (logandc2 (theory-info-code thn1) (theory-info-code thn2))))

(defun theory-info-is-restriction-of-ignoring-id (thn1 thn2)
  (= 0 (logandc2 (theory-info-code thn1)
                 (logior .Z. (theory-info-code thn2)))))


;;; ****************
;;; UTILS FOR THEORY____________________________________________________________
;;; ****************

;;; E-EQUAL-IN-THEORY : Theory Term Term -> Bool
;;;-----------------------------------------------------------------------------
;;; Returns true iff the two terms "t1" and "t2" are E-equal in the theory "th"
;;; which the theory of the top symbol of "t1".
;;; Supposes that "t1" and "t2" are already in standard form.
;;;

(defmacro E-equal-in-theory (_th _t1 _t2 &optional (_unify? nil))
  (if _unify?
      `(funcall (theory-info-unify-equal-fun (theory-info ,_th)) ,_t1 ,_t2)
      `(funcall (theory-info-match-equal-fun (theory-info ,_th)) ,_t1 ,_t2)))

#|| not used
(defun E-equal-in-theory-direct (th t1 t2 &optional (unify? nil))
  (let ((theory-info (theory-info th)))
    (cond ((or (theory-info-is-empty theory-info)
               (theory-info-is-Z theory-info)
               (theory-info-is-I theory-info)
               (theory-info-is-IZ theory-info))
           (if unify?
               (unify-empty-equal t1 t2)
               (match-empty-equal t1 t2)))
          ((or (theory-info-is-AC theory-info)
               (theory-info-is-ACI theory-info)
               (theory-info-is-ACZ theory-info)
               (theory-info-is-ACIZ theory-info))
           (if unify?
               (unify-AC-equal t1 t2)
               (match-AC-equal t1 t2)))
          ((or (theory-info-is-A theory-info)   
               (theory-info-is-AI theory-info)
               (theory-info-is-AZ theory-info)
               (theory-info-is-AIZ theory-info))
           (if unify?
               (unify-A-equal t1 t2)
               (match-A-equal t1 t2)))
          ((or (theory-info-is-C theory-info)
               (theory-info-is-CI theory-info)
               (theory-info-is-CZ theory-info)
               (theory-info-is-CIZ theory-info))
           (if unify?
               (unify-C-equal t1 t2)
               (match-C-equal t1 t2))))))

||#

;;; ************************
;;; THEORY PROPERTY TESTERS ____________________________________________________
;;; ************************

;;; returns true iff the theory "th" contains the associativity axiom
;;;
(defmacro theory-contains-associativity (*th)
  `(test-theory .A. (theory-info-code (theory-info ,*th))))

(defun theory-contains-associativity-direct (th)
  (let ((theory-info (theory-info th)))
    (and (not (theory-info-is-empty theory-info))
         (or (theory-info-is-A theory-info) 
             (theory-info-is-AC theory-info) 
             (theory-info-is-AI theory-info) 
             (theory-info-is-AZ theory-info) 
             (theory-info-is-AIZ theory-info) 
             (theory-info-is-ACI theory-info)
             (theory-info-is-ACZ theory-info) 
             (theory-info-is-ACIZ theory-info)))))

;;; returns true iff the theory "th" contains the commutativity axiom
;;;
(defmacro theory-contains-commutativity (*th)
  `(test-theory .C. (theory-info-code (theory-info ,*th))))

(defun theory-contains-commutativity-direct (th)
  (let ((theory-info (theory-info th)))
    (and (not (theory-info-is-empty theory-info))
         (or (theory-info-is-C theory-info) 
             (theory-info-is-AC theory-info) 
             (theory-info-is-CI theory-info) 
             (theory-info-is-CZ theory-info) 
             (theory-info-is-CIZ theory-info) 
             (theory-info-is-ACI theory-info)
             (theory-info-is-ACZ theory-info) 
             (theory-info-is-ACIZ theory-info)))))

(defmacro theory-contains-AC (*th)
  `(test-theory .AC. (theory-info-code (theory-info ,*th))))

(defun theory-contains-AC-direct (th)
  (let ((theory-info (theory-info th)))
    (or (theory-info-is-AC theory-info) 
        (theory-info-is-ACZ theory-info)
        (theory-info-is-ACI theory-info)
        (theory-info-is-ACIZ theory-info))))

;;; returns true iff the theory "th" contains the idempotency axiom
;;;
(defmacro theory-contains-idempotency (*th)
  `(test-theory .I. (theory-info-code (theory-info ,*th))))

(defun theory-contains-idempotency-direct (th)
  (let ((theory-info (theory-info th)))
    (or (theory-info-is-I theory-info) 
        (theory-info-is-CI theory-info) 
        (theory-info-is-IZ theory-info) 
        (theory-info-is-AI theory-info) 
        (theory-info-is-AIZ theory-info) 
        (theory-info-is-ACI theory-info)
        (theory-info-is-CIZ theory-info)
        (theory-info-is-ACIZ theory-info))))

;;; returns true iff the theory contains the identity axiom.
;;;
(defmacro theory-contains-identity (*th)
  `(test-theory .Z. (theory-info-code (theory-info ,*th))))

(defun theory-contains-identity-direct (th)
  (let ((theory-info (theory-info th)))
    (or (theory-info-is-Z theory-info) 
        (theory-info-is-CZ theory-info) 
        (theory-info-is-AZ theory-info) 
        (theory-info-is-IZ theory-info) 
        (theory-info-is-AIZ theory-info) 
        (theory-info-is-ACZ theory-info)
        (theory-info-is-CIZ theory-info)
        (theory-info-is-ACIZ theory-info))))

(defmacro theory-contains-ACZ (*th)
  `(test-theory .ACZ. (theory-info-code (theory-info ,*th))))

(defun theory-contains-ACZ-direct (th)
  (let ((theory-info (theory-info th)))
    (or (theory-info-is-ACZ theory-info)
        (theory-info-is-ACIZ theory-info))))

(defmacro theory-contains-AZ (*th)
  `(test-theory .AZ. (theory-info-code (theory-info ,*th))))

(defun theory-contains-AZ-direct (th)
  (let ((theory-info (theory-info th)))
    (or (theory-info-is-AZ theory-info)
        (theory-info-is-AIZ theory-info)
        (theory-info-is-ACZ theory-info)
        (theory-info-is-ACIZ theory-info))))

;;; EOF

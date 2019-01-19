;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
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
                                  Module: boot
                               File: preproc.lisp
==============================================================================|#

;;;*****************************************************************************
;;;                             Support procs of
;;;                     OBJ compatible Standard Prelude
;;;                                    +
;;;                      Chaos specific builtin modules
;;;*****************************************************************************

;;;-----------------------------------------------------------------------------
;;; module UNIVERSAL
;;;-----------------------------------------------------------------------------
;;(defun install-Universal ()
;;  (let ((UNIVERSAL (eval-modexp "UNIVERSAL")))
;;    (setf *universal-sort*
;;          (find-sort-in UNIVERSAL "Universal"))
;;    (setf *match-dep-var* (make-variable-term *universal-sort* 'REST))
;;    ))

;;; module PARSER
;;;-----------------------------------------------------------------------------
(defun token-is-sort-id (token)
  (and (stringp token)
       (<= 1 (length token))
       (find-all-sorts-in (get-context-module) token)))
(defun create-sort-id (token) token)
(defun print-sort-id (x) (princ x))
(defun is-sort-Id (x)
  (token-is-sort-id x))

;;;-----------------------------------------------------------------------------
;;;  module NZNAT
;;;-----------------------------------------------------------------------------
(defun is-NzNat-token (token)
  (and (stringp token)
       (every #'digit-char-p token)
       (some #'(lambda (ch) (not (eql #\0 ch))) token)))
(defun create-NzNat (token) (read-from-string token))
(defun is-NzNat (x) (and (integerp x) (< 0 x)))

;;;-----------------------------------------------------------------------------
;;; module NAT
;;;-----------------------------------------------------------------------------
(defun is-Zero-token (x) (equal "0" x))
(defun create-Zero (x) (declare (ignore x)) 0)
(defun is-Zero (x) (= 0 x))

(defun is-Nat-token (token) (declare (ignore token)) nil)
(defun create-Nat (token) (read-from-string token))
(defun is-Nat (x) (and (integerp x) (<= 0 x)))

;;;-----------------------------------------------------------------------------
;;; module INT
;;;-----------------------------------------------------------------------------
(defun is-NzInt-token (token)
  (and (stringp token)
       (general-read-numberp token)
       (<= 2 (length token))
       (eql #\- (char token 0))
       (some #'(lambda (ch) (not (eql #\0 ch))) token)))
(defun create-NzInt (x) (read-from-string x))
(defun is-NzInt (x) (and (integerp x) (not (= 0 x))))

(defun create-Int (token) (read-from-string token))
(defun is-Int-token (tok) (declare (ignore tok)) nil)
(defun print-Int (x) (prin1 x))
(defun is-Int (x) (integerp x))

;;;-----------------------------------------------------------------------------
;;; module RAT
;;;-----------------------------------------------------------------------------
(defun is-NzRat-token (token)
  (and (stringp token)
       (every #'(lambda (x)
                  (or (digit-char-p x)
                      (eql #\- x)
                      (eql #\/ x)))
              token)
       (let* ((first (if (eql #\- (char token 0)) 1 0))
              (slash (position #\/ token)))
         (and slash
              (is-NzNat-token (subseq token first slash))
              (is-NzNat-token (subseq token (+ slash 1)))))))
(defun create-NzRat (x) (read-from-string x))
(defun is-NzRat (x) (and (rationalp x) (not (= 0 x))))

(defun is-Rat-token (tok) (declare (ignore tok)) nil)
(defun create-Rat (x) (read-from-string x))
(defun RAT-print (x)
  (if (typep x 'ratio)
      (progn (prin1 (numerator x)) (princ "/") (prin1 (denominator x)))
    (prin1 x)))

;;;-----------------------------------------------------------------------------
;;; module ID
;;;-----------------------------------------------------------------------------
(defun is-Id-token (token)
  (and (stringp token)
       (not (numeric-char-p (char token 0)))
       (not (find #\. token))
       ;; (alpha-char-p (char token 0))
       (let ((pos (position #\: token))
             (len (length token)))
         (and (<= 1 len)
              (if pos
                  (= pos (1- len))
                t)))))
;; (defun create-Id (token) (intern token))
(defun create-Id (token) token)
;; (defun print-Id (x) (princ (string x)))
(defun print-Id (x) (princ x))
;; (defun is-Id (x)
;;  (and (symbolp x)
;;       (is-Id-token (symbol-name x))))
(defun is-Id (x)
  (and (string x)
       (is-Id-token x)))

;;;-----------------------------------------------------------------------------
;;; sort Qid
;;;-----------------------------------------------------------------------------
(defun is-qId-token (token)
  (and (stringp token)
       (<= 2 (length token))
       (eql #\' (char token 0))))
  
(defun create-qId (token)
  (intern token))

(defun print-qId (x) (format t "~a" (string x)))

(defun is-qId (x)
  (and (symbolp x)
       (is-qId-token (symbol-name x))))

(defun qid->string (obj)
  (string obj))

(defun string->qid (obj)
  (create-qId (concatenate 'string "'" obj)))

;;;-----------------------------------------------------------------------------
;;; sort Sort
;;;-----------------------------------------------------------------------------
(defun is-Sort-token (token)
  (and (stringp token)
       (<= 2 (length token))
       (eql #\' (char token 0))))
  
(defun create-Sort-object (token)
  (intern token))

(defun print-meta-sort-object (x) (format t "~a" (string x)))

(defun is-sort-object (x)
  (and (symbolp x)
       (is-sort-token (symbol-name x))))

;;;-----------------------------------------------------------------------------
;;; sort constant
;;;-----------------------------------------------------------------------------
(defun is-constant-token (token)
  (and (stringp token)
       (<= 2 (length token))
       (eql #\' (char token 0))
       (position #\. token :start 1)))
  
(defun create-constant-object (token)
  (intern token))

(defun print-constant-object (x) (format t "~a" (string x)))

(defun is-constant-object (x)
  (and (symbolp x)
       (is-constant-token (symbol-name x))))

;;;-----------------------------------------------------------------------------
;;; sort variable
;;;-----------------------------------------------------------------------------
(defun is-variable-token (token)
  (and (stringp token)
       (<= 2 (length token))
       (eql #\' (char token 0))
       (position #\: token :start 1)))
  
(defun create-variable-object (token)
  (if (eql #\' (char token 0))
      (intern (subseq token 1))
    (intern token)))

(defun print-variable-object (x) (format t "'~a" (string x)))

(defun is-variable-object (x)
  (and (symbolp x)
       (is-variable-token (symbol-name x))))

;;;-----------------------------------------------------------------------------
;;; module FLOAT
;;;-----------------------------------------------------------------------------
(defun is-Float-token (token)
  (and (stringp token)
       (let ((chars (coerce token 'list)))
         (and (<= 2 (length chars))
              (member #\. chars)))
       (multiple-value-bind (res len) (read-from-string token)
         (and (= (length token) len)
              (member (type-of res)
                      '(float long-float short-float fixnum bignum ratio
                        single-float double-float))))))

(defun create-Float (token)
  (coerce (read-from-string token) 'long-float))
(defun print-Float (val) (prin1 val))
(defun is-Float (val) (typep val 'float))

;;;-----------------------------------------------------------------------------
;;; ChaosValue Builtin Sort
;;;-----------------------------------------------------------------------------
(defmacro is-compiled-chaos-value (_val)
  `(and (consp ,_val)
        (eq (car ,_val) '|%Chaos|)))

(defun print-chaos-value (val)
  (print-chaos-object val))

(defun is-variable? (val)
  (and (term? val) (term-is-variable? val)))

(defun is-applform? (val)
  (and (term? val) (term-is-applform? val)))

(defun is-pvariable? (val)
  (and (term? val) (term-is-pconstant? val)))

(defun is-lisp-form? (val)
  (and (term? val) (term-is-lisp-form? val)))

(defun is-slisp-form? (val)
  (and (term? val) (term-is-simple-lisp-form? val)))

(defun is-glisp-form? (val)
  (and (term? val) (term-is-general-lisp-form? val)))

(defun is-bconst-term? (val)
  (and (term? val) (term-is-builtin-constant? val)))

;;;-----------------------------------------------------------------------------
;;; TRUTH-VALUE, TRUTH & BOOL
;;;-----------------------------------------------------------------------------
;;;
(defun setup-truth-value ()
  (setq *truth-value-module* (eval-modexp "TRUTH-VALUE"))
  (prepare-for-parsing *truth-value-module*)
  (with-in-module (*truth-value-module*)
    (setq *bool-sort*
          (find-sort-in *truth-value-module* "Bool"))
    (setq *condition-sort*
      (find-sort-in *truth-value-module* "*Condition*"))
    (let* ((t-opinfo (find-operator '("true") 0 *truth-value-module*))
           (f-opinfo (find-operator '("false") 0 *truth-value-module*))
           (t-meth (lowest-method* (car (opinfo-methods t-opinfo))))
           (f-meth (lowest-method* (car (opinfo-methods f-opinfo)))))
      (setq *BOOL-true* (make-applform *bool-sort*
                                       t-meth
                                       nil))
      (setq *bool-true-meth* t-meth)
      (setq *bool-false* (make-applform *bool-sort*
                                        f-meth
                                        nil))
      (setq *bool-false-meth* f-meth))))
      
;;; op bool-make-conjunction : Term Term -> Term
;;;
(defun BOOL-make-conjunction (t1 t2)
  (make-applform *bool-sort* *bool-and* (list t1 t2)))

;;; op coerce-to-Bool : Lisp -> Bool
;;;
(defun coerce-to-Bool (x)
  (if x *BOOL-true* *BOOL-false*))

;;;-----------------------------------------------------------------------------
;;; ID
;;;-----------------------------------------------------------------------------
(defun setup-id ()
  (setq *id-module* (eval-modexp "ID"))
  (final-setup *id-module*)
  (with-in-module (*id-module*)
    (setq *id-sort* (find-sort-in *id-module* "Id"))))

;;;-----------------------------------------------------------------------------
;;; module CHARACTER
;;;-----------------------------------------------------------------------------

;;; INSTALL-CHARACTER

(defun install-character ()
  (let ((char-module (eval-modexp "CHAR-VALUE")))
    (if (and char-module (not (modexp-is-error char-module)))
        (let ((c-sort (find-sort-in char-module "Character")))
          (if c-sort
              (setq *character-sort* c-sort)
              (with-output-panic-message ()
                (princ "could not find Character sort in module CHAR-VALUE"))))
        (with-output-panic-message ()
          (princ "Could not find module CHAR-VALUE.")
          (break)))))

;;; character-token ::= 'char'
;;;            char ::= <alphanumeric>
;;;
(defun is-character-token (tok)
  (and (stringp tok)
       (let ((len (length tok)))
         (and (< 2 len)
              (eql (char tok 0) #\')
              (eql (char tok (1- len)) #\')
              (let ((first-char (char tok 1)))
                (case first-char
                  (#\\                  ; escape
                   (or (every #'(lambda (x) (digit-char-p x)) (subseq tok 2 (1- len)))
                       (= len 4)))
                  (t (= len 3))))))))

(defun create-character (tok)
  (let ((len (length tok)))
    (if (= 3 len)
        (char tok 1)
        (let ((first-char (char tok 2)))
          (if (digit-char-p first-char)
              (let ((num (read-from-string (subseq tok 2 (1- len)))))
                (if (< num char-code-limit)
                    (code-char num)
                    (with-output-chaos-error ('invalid-char-code)
                      (format t "invalid character code '\\~d' is given" num)
                      )))
              (case first-char
                (#\n #\newline)
                (#\l #\linefeed)
                (#\t #\tab)
                (#\s #\space)
                (#\p #\page)
                (otherwise first-char)))))))

(defun is-character (obj) (characterp obj))

(defun print-character (obj)
  (if (graphic-char-p obj)
      (if (eql obj #\space)
          (princ "'\\s'")
          (format t "'~a'" obj))
      (case obj
        (#\newline (princ "'\\n'"))
        ;; #-:CLISP (#\linefeed (princ "'\\l'"))
        (#\tab (princ "'\\t'"))
        (#\space (princ "'\\s'"))
        (#\page (princ "'\\p'"))
        (otherwise (format t "'\\~d'" (char-code obj))))))
      
;;;-----------------------------------------------------------------------------
;;; module STRING
;;;-----------------------------------------------------------------------------
(defun install-string ()
  (let ((string-module (eval-modexp "STRING-VALUE")))
    (if (and string-module (not (modexp-is-error string-module)))
        (let ((s-sort (find-sort-in string-module "String")))
          (if s-sort
              (setq *string-sort* s-sort)
              (with-output-panic-message()
                (princ "could not find String sort in module STRING-VALUE"))))
        (with-output-panic-message()
          (princ "Could not find module STRING-VALUE.")
          (break)))))

(defun s-find (Char Str Num)
  (let ((C (term-builtin-value Char))
        (S (term-builtin-value Str))
        (N (term-builtin-value Num)))
    (let ((pos (position C S :start N)))
      (if pos
          (simple-parse-from-string (format nil "~s" pos))
        (simple-parse-from-string "notFound")))))

(defun s-rfind (Char Str Num)
  (let ((C (term-builtin-value char))
        (S (term-builtin-value Str))
        (N (term-builtin-value Num)))
    (let ((pos (position C S :start N :from-end t)))
      (if pos
          (simple-parse-from-string (format nil "~s" pos))
        (simple-parse-from-string "notFound")))))

;;; EOF

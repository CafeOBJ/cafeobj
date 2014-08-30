;;;-*- Mode:Lisp; Syntax:Common-Lisp; Package:CHAOS -*-
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
(in-package :CHAOS)
#|==============================================================================
                                 System: Chaos
                                 Module: comlib
                               File: macros.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;;== DESCTIPTION ==============================================================
;;;   A collection of misc utility macros.

;;; *******
;;; DECLAIM_____________________________________________________________________
;;; *******
;;;#-(or cltl2 GCL)
;;;(defmacro declaim (arg) `(proclaim ',arg))

;;; ****************
;;; FAMOUS ONCE-ONLY____________________________________________________________
;;; ****************

(defmacro once-only (vars &body body)
  (let ((gensym-var (gensym))
        (run-time-vars (gensym))
        (run-time-vals (gensym))
        (expand-time-val-forms ()))
    (dolist (var vars)
      (push `(if (or (symbolp ,var)
                     (numberp ,var)
                     (and (listp ,var)
                          (member (car ,var) '(quote function))))
                 ,var
                 (let ((,gensym-var (gensym)))
                   (push ,gensym-var ,run-time-vars)
                   (push ,var ,run-time-vals)
                   ,gensym-var))
            expand-time-val-forms))    
    `(let* (,run-time-vars
            ,run-time-vals
            (wrapped-body
              (let ,(mapcar #'list vars (reverse expand-time-val-forms))
                ,@body)))
       `(let ,(mapcar #'list (reverse ,run-time-vars)
                             (reverse ,run-time-vals))
          ,wrapped-body))))

;;; *********************************
;;; Specialized MEMBER/ASSOC/POSITION___________________________________________
;;; *********************************

#-:ccl
(defmacro memq (item list) `(member ,item ,list :test #'eq))
#-:ccl
(defmacro assq (item list) `(assoc ,item ,list :test #'eq))
(defmacro posq (item list) `(position ,item ,list :test #'eq))
(defmacro memeq (item list) `(member ,item ,list :test #'equal))
(defmacro asseq (item list) `(assoc ,item ,list :test #'equal))
(defmacro poseq (item list) `(position ,item ,list :test #'equal))

;;; **********
;;; CASE-EQUAL__________________________________________________________________
;;; **********
;;; same as normal `case' test by equal instead of eql.

(defmacro case-equal (keyform &rest clauses &aux (form nil) (key (gensym)))
  (dolist (clause (reverse clauses) `(let ((,key ,keyform)) ,form))
    #+GCL (declare (object clause))
    (cond ((or (eq (car clause) 't) (eq (car clause) 'otherwise))
           (setq form `(progn ,@(cdr clause))))
          ((consp (car clause))
           (setq form `(if (member ,key ',(car clause) :test #'equal)
                           (progn ,@(cdr clause))
                           ,form)))
          ((car clause)
           (setq form `(if (equal ,key ',(car clause))
                           (progn ,@(cdr clause))
                           ,form)))))
  )


;;; **************
;;; DOTIMES-FIXNUM______________________________________________________________
;;; **************
;;; FROM OBJ3 implementation by Tim.Winkler of SRI.
;;; I don't know how this could be efficient in general, but for GCL(KCL..) this
;;; works well.
;;;
(defmacro dotimes-fixnum (&rest body)
  (let ((var (car (car body)))
        (lim (cadr (car body)))
        (res (cddr (car body)))
        (acts (cdr body))
        (limvar (gensym))
        (lab (gensym)))
    ` (block ()
        (let* ((,limvar ,lim) (,var 0))
          (declare (type fixnum ,var ,limvar))
          (tagbody
             ,lab
             (if (>= ,var ,limvar) (return (progn ,@res)))
             (tagbody ,@acts)
             (setf (the fixnum ,var) (the fixnum (1+ (the fixnum ,var))))
             (go ,lab)))))
  )

;;; ****************
;;; Syntactic Sugars____________________________________________________________
;;; ****************

(defmacro msetq (vars value)
 `(multiple-value-setq ,vars ,value))

(defmacro mlet (vars value &body body)
  `(multiple-value-bind ,vars ,value ,@body))

;;; let-if
;;;  Binds let arguments only if condition is non-nil, and evaluates body
;;;  in any case.

(defmacro let-if (condition bindings &body body)
  `(if ,condition
       (let ,bindings
         ,@body)
       (progn ,@(if (eq (caar body) 'declare) (cdr body) body))))

;;; when-bind
;;;  Binds the symbol to predicate and executes body only if predicate
;;;  is non-nil."

(defmacro when-bind ((symbol predicate) &body body)
  `(let ((,symbol ,predicate))
     (when ,symbol
       ,@body)))

;;; while
;;;  Keeps invoking the body while the test is true; test is tested before each
;;;  loop.
  
;;;; #-(or :allegro-v6.0 :allegro-v6.1 :allegro-v6.2 :allegro-v7.0 :allegro-v8.0)
#-(or :allegro)
(defmacro while (test &body body)
  (let ((end-test (gensym))
        (loop (gensym)))
    `(block nil
       (tagbody (go ,end-test) 
                ,loop
                ,@body
                ,end-test
                (when ,test (go ,loop))
                (return)))))

;;; while-not
;;;  Keeps invoking the body while the test is not true;  test is tested before
;;;  each loop.

(defmacro while-not (test &body body)
  (let ((end-test (gensym))
        (loop (gensym)))
    `(block nil
       (tagbody (go ,end-test) 
                ,loop
                ,@body
                ,end-test
                (unless ,test (go ,loop))
                (return)))))

;;; def-synonym sym1 sym2
;;; 
(defmacro def-synonym (sym1 sym2)
  `(setf (symbol-function ',sym1)
     (symbol-function ',sym2)))

;;;
;;; #-:excl
#-(or :excl ccl)
(defmacro fixnump (num)
  `(typep ,num 'fixnum))

;;; EOF

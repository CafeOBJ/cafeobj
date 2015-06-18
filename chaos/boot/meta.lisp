;;;-*-Mode:LISP; Package: Chaos; Base:10; Syntax:Common-lisp -*-
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
(in-package :chaos)
#|==============================================================================
                                 System: Chaos
                           Module: primitives.chaos
                                File: meta.lisp
===============================================================================|#
;;;
;;;
;;;
;;; ************
;;; SystemObject
;;; ************
(eval-when (:compile-toplevel :load-toplevel :execute)
(defun clear-metalevel-sort ()
  (clrhash *builtin-metalevel-sort*))

(defun register-metalevel-sort (sort)
  (setf (gethash sort *builtin-metalevel-sort*) t))

  (clear-metalevel-sort)
  
(defstruct (chaos-list (:print-function pr-chaos-list))
  (list nil))

;;; MetaLevel builtin constants
;;; empty *CafeList* :[]
(defparameter *chaos-null* (make-chaos-list))
)

(defun mnth (chaos-list num)
  (and (chaos-list-p chaos-list)
       (or (nth num (chaos-list-list chaos-list))
           *chaos-null*)))

(defun mnthcdr (chaos-list num)
  (and (chaos-list-p chaos-list)
       (or (nthcdr num (chaos-list-list chaos-list))
           *chaos-null*)))

(defun mlength (chaos-list)
  (and (chaos-list-p chaos-list)
       (length (chaos-list-list chaos-list))))

(defun pr-chaos-list (obj stream &rest ignore)
  (declare (ignore ignore))
  (let ((lst (chaos-list-list obj)))
    (if lst
        (format stream ":[~s]" lst)
      (format stream ":[]"))))

;;; 
;;; META LEVEL TERM
;;;
(defun make-meta-term (term)
  (if term
      (make-applform *term-sort* *op-term* (list term))
    (create-system-object-term nil)))

(defun meta-term-term (meta-term)
  (if (sort= (term-sort meta-term) *term-sort*)
      (term-arg-1 meta-term)
    meta-term))

;;;
;;; CREATE-SYSTEM-OBJECT-TERM
;;;
(defun create-system-object-term (obj &optional (module *current-module*))
  (if (and (termp obj) (term-is-system-object? obj))
      obj
    (with-in-module (module)
      (let ((sort (cond ((null obj) *chaos-void-sort*)
                        ((symbolp obj) *chaos-void-sort*)
                        ((sort-p obj) *sort-sort*)
                        ((method-p obj) *operator-sort*)
                        ((module-p obj) *module-sort*)
                        ((axiom-p obj) *axiom-sort*)
                        ((termp obj) *term-sort*)
                        ((chaos-list-p obj) *chaos-list-sort*)
                        ((subst*-p obj) *subst-sort*)
                        ((signature-struct-p obj) *signature-sort*)
                        ((axiom-set-p obj) *axiomset-sort*)
                        ((trs-p obj) *trs-sort*)
                        ((is-ast obj) *chaos-expr-sort*)
                        (t *chaos-void-sort*))))
        (if (sort= sort *term-sort*)
            (make-meta-term obj)
          (if (sort= sort *chaos-void-sort*)
              (make-system-object-term 'void *chaos-void-sort*)
            (make-system-object-term obj sort)))))))

;;; msubterms
(defun msubterms (term)
  (and (termp term)
       (term-is-applform? term)
       (make-chaos-list :list (term-subterms term))))

;;; mterm-sort
(defun mterm-sort (term)
  (and (termp term)
       (term-sort term)))

;;; 
#||
(defun create-list-of-objects (fun system-obj-term)
  (create-system-object-term (mapcar #'(lambda (x) (create-system-object-term x))
                                     (funcall fun (term-system-object system-obj-term)))))
||#

#||
(defun create-list-of-objects (fun system-obj-term)
  (let ((vals (funcall fun (term-system-object system-obj-term))))
    (if vals
        (create-system-object-term (make-chaos-list :list (mapcar #'(lambda (x) (create-system-object-term x)) vals)))
      (create-system-object-term *chaos-null*))))
||#

(defun create-list-of-objects (fun system-obj-term)
  (let ((vals (funcall fun (term-system-object system-obj-term))))
    (if vals
        (make-chaos-list :list (mapcar #'(lambda (x) (create-system-object-term x)) vals))
      *chaos-null*)))

(defun do-apply!! (fun args)
  (let ((rfun (symbol-function (intern (term-builtin-value fun))))
        (rargs (if (and (sort= *cosmos* (term-sort args))
                        (term-is-application-form? args)
                        (equal (method-symbol (term-head args)) '("_" "," "_")))
                   (list-assoc-subterms args (term-head args))
                 (list args))))
      (if rfun
          (apply rfun rargs)
        (create-system-object-term nil))))

(defun do-apply! (&rest all)
  (format t "~s" all)
  (create-system-object-term all))

(defun create-chaos-list (&rest obj)
  (create-system-object-term (make-chaos-list :list obj)))

(defun bvalue (term)
  (if (term-is-builtin-constant? term)
      (term-builtin-value term)
    nil))

;;; ***************************
;;; META LEVEL SORT OPERATIONS
;;; ***************************
(defun sort-compare (pred s1 s2)
  (unless *current-module*
    (with-output-chaos-error ('not-context)
      (format t "No context module is specified.")))
  (case pred
    (< (sort< s1 s2))
    (<= (sort<= s1 s2))
    (t nil)))

(defun in-same-cc (s1 s2)
  (if (not *current-module*)
      (with-output-chaos-error ('no-current-module)
        (format t "Context module is not set"))
    (with-in-module (*current-module*)
      (is-in-same-connected-component s1 s2 *current-sort-order*))))

;;; **************
;;; *SUBSTITUTION*
;;; **************

(defstruct (subst* (:print-function pr-subst))
  (bindings nil))

(defun create-new-subst ()
  (make-subst* :bindings (new-substitution)))

(defun pr-subst (obj stream &rest ignore)
  (declare (ignore ignore))
  (print-substitution (subst*-bindings obj) stream))

(defun meta-get-context-module (module)
  (let ((rmod (if (termp module)
                  (cond ((and (termp module) (term-is-system-object? module))
                         (term-system-object module))
                        ((and (term-is-builtin-constant? module)
                              (sort= (term-sort module) *string-sort*))
                         (eval-modexp (term-builtin-value module)))
                        (t :invalid))
                (if (module-p module)
                    module
                  :invalid-modexp))))
    (if (or (eq rmod :invalid) (eq rmod :invalid-modexp))
        (with-output-chaos-error ('invalid-module)
          (format t "Invalid module specification ~S" module))
      rmod)))

(defun meta-get-term (pterm &optional (module *current-module*))
  (unless (termp pterm)
    (with-output-chaos-error ('ivalid-term)
      (format t "Invalid representation of meta term ~S" pterm)))
  (with-in-module (module)
    (let ((rterm pterm))
      (cond ((sort= (term-sort pterm) *term-sort*)
             (setq rterm (term-arg-1 pterm)))
            ((and (term-is-builtin-constant? pterm)
                  (sort= (term-sort pterm) *string-sort*))
             (setq rterm (simple-parse *current-module*
                                       (term-builtin-value pterm)
                                       *cosmos*))
             (when (term-is-an-error rterm)
               (with-output-chaos-error ('invalid-term)
                 (format t "Could not parse: ~S" (term-builtin-value pterm)))))
             (t rterm))
      rterm)))

(defun meta-get-integer (pterm &optional (module *current-module*))
  (let ((rterm (meta-get-term pterm module))
        (value nil))
    (when (term-is-builtin-constant? rterm)
      (setq value (term-builtin-value rterm)))
    (unless (integerp value)
      (with-output-chaos-error ('ivalid-integer)
        (format t "Invlid number specification ~S" pterm)))
    value))

(defun meta-get-list-integers (pterm &optional (module *current-module*))
  (if (and (consp pterm)
           (every #'integerp pterm))
      pterm
    (let ((rterm (meta-get-term pterm module)))
      (unless (chaos-list-p rterm)
        (with-output-chaos-error ('invalid-integers)
          (format t "Invalid integer list ~S" pterm)))
      (meta-get-list-integers (chaos-list-list rterm)))))

(defvar *meta-match-depth* 0)
(defvar *use-choose-match* nil)

(defun do-meta-match (target pattern &optional (module *current-module*)
                                               depth
                                               (type :match)
                                               (start-pos nil))
  (let* ((rmod (meta-get-context-module module))
         (rtarget (meta-get-term target))
         (rpattern (meta-get-term pattern))
         (rdepth (if depth (meta-get-integer pattern) -1))
         (rpos (if start-pos (meta-get-list-integers start-pos rmod) nil))
         (*meta-match-depth* 0))
    (with-in-module (rmod)
      (when rpos
        (setq rtarget (get-subterm-pos rtarget rpos)))
      (let ((real-target (if (eq type :match)
                             (supply-psuedo-variables rtarget)
                           rtarget)))
        (let ((first-match-meth (if (eq type :match)
                                    (if *use-choose-match*
                                        nil
                                      '@matcher)
                                  'first-unify))
              (next-match-meth (if (eq type :match)
                                   (if *use-choose-match*
                                       nil
                                     'next-match)
                                 'next-unify))
              ;; (result nil)
              )
          (when (and *use-choose-match*
                     (eq type :match))
            (let ((meth (choose-match-method real-target *bool-true* nil)))
              (setf first-match-meth (car meth))
              (setf next-match-meth (cdr meth))))
          ;; 
          (perform-meta-match* real-target rpattern rdepth first-match-meth next-match-meth))))))
    
#||
(defun perform-meta-match* (target pattern depth fm nm)
  (let 

        ;; ---- first match 
        (multiple-value-bind (global-state subst no-match e-equal)
            (funcall first-match-meth pattern real-target)
          (when no-match
            (if (eq type :match)
                (format t "~&-- no match")
              (format t "~&-- no unify"))
            (return-from do-meta-match *chaos-null*))
          (if (eq type :match)
              (format t "~&-- match success.")
            (format t "~&-- unify success."))
          (when e-equal
            (format t "~&-- given terms are equational equal.")
            (return-from do-meta-match *chaos-null*))
          (push (make-subst* :bindings subst) result)
          (multiple-value-setq (global-state subst no-match)
            (funcall next-match-meth global-state))
          (while (not no-match)
            (push (make-subst* :bindings subst) result)
            (multiple-value-setq (global-state subst no-match)
              (funcall next-match-meth global-state)))
          (make-chaos-list :list (nreverse result)))))

||#

(defun meta-subst-image (term sub)
  (let ((subst (subst*-bindings sub))
        (image nil))
    (setq image (substitution-image subst term))
    (make-meta-term image)))

;;;
;;; META-OCCUR-AT
;;;
(defun meta-get-occur (oc)
  (let ((oc-list (list-assoc-subterms oc (term-head oc))))
    (if oc-list
        (mapcar #'(lambda (x) (term-builtin-value x)) oc-list)
      nil)))

(defun meta-occur-at (t1 occur)
  (let ((term (meta-term-term t1))
        (roccur (meta-get-occur occur))
        (res nil))
    (setq res (subterm-op term roccur))
    (if res
        (make-meta-term res)
      (make-meta-term nil))))

;;; TODO
(defun subterm-op (&rest ignore)
  ignore)

(defun perform-meta-match* (&rest ignore)
  ignore)

(defun check-rwl-coherency (&rest ignore)
  ignore)

;;; EOF



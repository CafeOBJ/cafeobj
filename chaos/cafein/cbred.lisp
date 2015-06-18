;;;-*- Mode:LISP; Package: CHAOS; Base:10; Syntax:Common-lisp -*-
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
#|=============================================================================
                                  System:CHAOS
                                 Module:cafein
                                File:cbred.lisp
=============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 1) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; FLAGS
(declaim (special *cbred-trace-flag*))
(defvar *cbred-trace-flag* nil)

;;; GLOBALS
(declaim (special *cobasis*
                  *cobasis-ops*
                  *co-rules*))
(defvar *cobasis* nil)
(defvar *cobasis-ops* nil)
(defvar *co-rules* nil)

;;; *COBASIS* -----------------------------
;;; (((hidden-vars) . pattern) ....)

(defun make-cobasis-pattern (op)
  (let ((hidden-vars nil)
        (pattern nil))
    (setq pattern
      (make-term-with-sort-check
       op
       (mapcar #'(lambda (s)
                   (if (sort-is-hidden s)
                       (let ((hvar (make-variable-term s
                                                       (gensym "_H"))))
                         (push hvar hidden-vars)
                         hvar)
                     (make-variable-term s
                                         (gensym "_V"))))
               (method-arity op))))
    (cons (nreverse hidden-vars) pattern)
    ))

(defvar .cbred-new-variable-name. nil)
(let ((varnum 0))
  
(defun cbred-make-new-variable (var)
  (let ((vnam (incf varnum)))
    (if .cbred-new-variable-name.
        (make-variable-term (variable-sort var)
                            vnam
                            vnam)
      (make-variable-term (variable-sort var)
                          vnam
                          (variable-print-name var))
      )))
)

(defun expand-goal-by-cob (pair cob)
  (flet ((expand (term cob)
           (let ((subst-vars (car cob))
                 (subst-pat (cdr cob))
                 (subst nil))
             (dolist (v subst-vars)
               (when (sort<= (term-sort term) (term-sort v))
                 (push (cons v term) subst)))
             (apply-subst subst subst-pat))))
    (let ((lhs (expand (car pair) cob))
          (rhs (expand (cdr pair) cob)))
      (let ((vars (append (term-variables lhs)
                          (term-variables rhs)))
            (subst nil))
        (setq vars (delete-duplicates vars))
        (dolist (v vars)
          (push (cons v (cbred-make-new-variable v))
                subst))
        (setq lhs (apply-subst subst lhs))
        (setq rhs (apply-subst subst rhs))
        (cons lhs rhs)))
    ))

;;; *CO-RULES* ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
;;;  ( <rule> ... <rule> )
(defun apply-co-rules (target)
  (let ((applied nil))
    (labels ((apply-it (term)
               (when (term-is-applform? term)
                 (unless (memq (term-head term) *cobasis-ops*)
                   (dolist (sub (term-subterms term))
                     (apply-it sub)))
                 (dolist (rule *co-rules*)
                   #||
                   (format t "~%co-rule: ")
                   (print-rule-internal rule)
                   (format t "~%target: ")
                   (term-print term)
                   ||#
                   (if (apply-one-rule rule term)
                       (pushnew (car (rule-labels rule)) applied)))
                 )))
      (apply-it (car target))
      (apply-it (cdr target))

      (when applied
        (rewrite* (car target))
        (rewrite* (cdr target)))

      (if (term-equational-equal (car target)
                                 (cdr target))
          (values t (nreverse applied))
        (values nil (nreverse applied)))
      )))

;;; -------------------------------
;;; Circular Coinductive Rewriting:
;;; -------------------------------

(defun cbred-print-term-pair (pair &optional (stream *standard-output*))
  (let ((*standard-output* stream))
    (let* ((.file-col. (file-column stream))
           (*print-indent* (if (= 0 .file-col.)
                               (+ 4 *print-indent*)
                             .file-col.))
           (.printed-vars-so-far. nil))
      (setq .printed-vars-so-far.
        (term-print (car pair)))
      (setq .file-col. (file-column stream))
      (if (print-check 0 .file-col.)
          (princ "== ")
        (princ " == "))
      (setq .file-col. (file-column stream))
      (if (not (= 0 .file-col.))
          (setq *print-indent* .file-col.))
      (term-print (cdr pair))
      )))

(let ((.crule-label-num. 0))
  (defun reset-crule-label ()
    (setq .crule-label-num. 0))
  (defun next-crule-label ()
    (intern (format nil "c~D" (incf .crule-label-num.))))
  )

(defun cbred-goal (pair)
  (let ((rule-count *rule-count*))
    (let ((lhs (rewrite* (car pair)))
          (rhs (rewrite* (cdr pair))))
      (if (term-equational-equal lhs rhs)
          (values t lhs)
        (values nil (not (= rule-count *rule-count*)))
      ))))

;;;
(defun find-occ (term predicate occr &optional (num-if 0))
  (when (funcall predicate term)
    (return-from find-occ (values occr num-if)))
  ;;
  (if (and (term-is-applform? term)
           (eq (term-head term) *bool-if*))
      (multiple-value-bind (occr1 num-if-1)
          (find-occ (term-arg-2 term) predicate occr (1+ num-if))
        (multiple-value-bind (occr2 num-if-2)
            (find-occ (term-arg-3 term) predicate occr (1+ num-if))
          (if (listp occr1)
              (if (listp occr2)
                  (if (<= (length occr1) (length occr2))
                      (values occr2 num-if-2)
                    (values occr1 num-if-1))
                (values occr1 num-if-1))
            (if (listp occr2)
                (values occr2 num-if-2)
              (values :no (1+ num-if))))))
    (if (not (term-is-applform? term))
        (values :no num-if)
      (progn
        (dotimes (x (length (term-subterms term)))
          (multiple-value-bind (res new-num-if)
              (find-occ (term-arg-n term x)
                        predicate
                        (cons x occr)
                        num-if)
            (if (listp res)
                (return-from find-occ (values res new-num-if)))))
        (values :no num-if))
      )))

#||
(defun cbred-orient-rule (pair)
  (let ((lhs (car pair))
        (rhs (cdr pair)))
    (return-from cbred-orient-rule (values lhs rhs))
    (let ((occ (find-occ lhs #'(lambda (x)
                                 (and (sort-is-hidden (term-sort x))
                                      (not (memq (term-head x)
                                                 *cobasis-ops*))))
                         nil)))
      (unless (listp occ) (return-from cbred-orient-rule nil))
      (let ((context lhs)
            (head nil))
        (dolist (c (reverse occ))
          (setq context (term-arg-n context c)))
        (setq head (term-head context))
        (let ((rocc (find-occ rhs #'(lambda (x)
                                      (and (term-is-applform? x)
                                           (method-is-of-same-operator
                                            head
                                            (term-head x))))
                              nil)))
          (if (or (not (listp rocc))
                  (>= (length occ) (length rocc)))
              (values lhs rhs)
            (values rhs lhs))
          ))
      )))
||#

#+:allegro
(defun cbred-orient-rule (pair)
  (if (featurep :bigpink)
      (pn-orient-term-pair *current-module*
                           pair)
    (values (car pair) (cdr pair))))

#-:allegro
(defun cbred-orient-rule (pair)
  (values (car pair) (cdr pair)))

(defun add-new-crule (pair)
  (multiple-value-bind (lhs rhs)
      (cbred-orient-rule pair)
    (unless lhs
      (with-output-panic-message ()
        (let ((.printed-vars-so-far. nil))
          (princ "could not find any hidden context.")
          (print-next)
          (princ "this should not happen")
          (print-next)
          (setq .printed-vars-so-far. (term-print (car pair)))
          (print-next)
          (term-print (cdr pair)))))
    (let ((new-crule (make-rule :lhs lhs
                                :rhs rhs
                                :condition *bool-true*
                                :labels (list (next-crule-label))
                                :behavioural t
                                :type :cbred-circle)))

      (setq *co-rules*
        (nconc *co-rules* (list new-crule)))
      ;; (push new-crule *co-rules*)
      (when *cbred-trace-flag*
        (with-output-simple-msg ()
          (princ "  add rule: ")
          (print-rule-internal new-crule)))
      )))

(defun term-contains-beh-context (term)
  (or (sort-is-hidden (term-sort term))
      (and (term-is-applform? term)
           (some #'(lambda (x) (term-contains-beh-context x))
                 (term-subterms term)))))

(defun cbred-deduce (pair)
  (let ((next-goals nil))
    (dolist (cob *cobasis*)
      (block next
        (let ((target (expand-goal-by-cob pair cob)))
          (when *cbred-trace-flag*
            (with-output-simple-msg ()
              (let ((.printed-vars-so-far. nil))
                (princ "---------------------------------------")
                (print-next)
                (princ "Target: ")
                (cbred-print-term-pair target))))
          (multiple-value-bind (ok? reduced)
              (cbred-goal target)
            (when ok?
              (when *cbred-trace-flag*
                (with-output-simple-msg ()
                  (princ "  reduced: true")
                  (print-next)
                  (princ "nf: ")
                  (term-print reduced)))
              (return-from next nil))
            (when reduced
              (when *cbred-trace-flag*
                (let ((.printed-vars-so-far. nil))
                  (with-output-simple-msg ()
                    (princ "  reduced: ")
                    (cbred-print-term-pair target)))))
            ;; try deduce with *co-rules*
            (multiple-value-bind (ok? applied)
                (apply-co-rules target)
              (when ok?
                (when *cbred-trace-flag*
                  (with-output-simple-msg ()
                    (format t "  deduced~a: true" applied)
                    (print-next)
                    (princ "nf: ")
                    (term-print (car target))))
                (return-from next nil))
              ;;
              #||
              (when (and (not (term-contains-beh-context (car target)))
                         (not (term-contains-beh-context (cdr target))))
                ;; failure
                (throw ':fail nil))
              ||#
              (when (or (not (sort-is-hidden (term-sort (car target))))
                        (and (memq (term-head (car target)) *cobasis-ops*)
                             (memq (term-head (cdr target)) *cobasis-ops*)))
                (throw ':fail nil))
              ;; ng
              (when applied 
                (when *cbred-trace-flag*
                  (let ((.printed-vars-so-far. nil))
                    (with-output-simple-msg ()
                      (format t "  deduced~a: " applied)
                      (cbred-print-term-pair target)))))
              ;;
              (unless (or reduced applied)
                (when *cbred-trace-flag*
                  (with-output-chaos-warning ()
                    (princ "!! no rules were applied.")
                    (print-next)))
                (throw ':fail nil))
              (add-new-crule target)
              (push target next-goals)))
          )))
    ;; done 
    next-goals
    ))
    
;;; MAIN

(defun do-cbred (module lhs rhs)
  (with-in-module (module)
    (reset-crule-label)
    (let ((lhs-sort (term-sort lhs))
          (rhs-sort (term-sort rhs))
          (sort nil)
          (**print-var-sort** nil))
      #||
      (unless (and (sort-is-hidden lhs-sort)
                   (sort-is-hidden rhs-sort))
        (with-output-chaos-error ('invalid-sort)
          (princ "cbred: terms must be of hidden sort.")))
      ||#
      (if (sort<= lhs-sort rhs-sort)
          (setq sort rhs-sort)
        (if (sort< rhs-sort lhs-sort)
            (setq sort lhs-sort)
          (with-output-chaos-error ('invalid-terms)
            (princ "cbred: pair of terms must of same sort family."))))
      ;;
      (let ((goals (list (cons lhs rhs)))
            (*co-rules* nil)
            (*cobasis* nil)
            (*cobasis-ops* nil)
            (*cbred-trace-flag* $$trace-rewrite)
            (ok? nil))
        (declare (special *cbred-trace-flag*)
                 (special *co-rules* *cobasis* *cobasis-ops*))
        ;; use own tracer
        (when *cbred-trace-flag*
          (trace-off))
        (dolist (cob (module-cobasis *current-module*))
          (when (some #'(lambda (s) (sort<= sort s))
                      (method-arity cob))
            (push (make-cobasis-pattern cob) *cobasis*)
            (push cob *cobasis-ops*)))
        (setq *cobasis* (nreverse *cobasis*))
        (setq *cobasis-ops* (nreverse *cobasis-ops*))
        ;;
        (when *cbred-trace-flag*
          (with-output-simple-msg ()
            (princ "** Cobasis:")
            (dolist (op *cobasis-ops*)
              (print-next)
              (print-chaos-object op))
            (print-next)
            (princ "-------------------------------------")
            ))
        ;;
        (multiple-value-bind (ok? reduced)
            (cbred-goal (car goals))
          (declare (ignore reduced))
          (when *cbred-trace-flag*
            (let ((.printed-vars-so-far. nil))
              (with-output-simple-msg ()
                (princ "  reduced to: ")
                (cbred-print-term-pair (car goals)))))
          (when ok?
            (when *cbred-trace-flag*
              (trace-on))
            (return-from do-cbred t)))
        ;;
        (add-new-crule (car goals))
        ;;
        ;; do the real work 
        ;; 
        (setq ok?
          (catch ':fail
            (loop
              (unless goals (return t))
              (let ((new-goals nil))
                (dolist (pair goals)
                  (setq new-goals
                    (nconc new-goals
                           (cbred-deduce pair))))
                (setq goals new-goals))
              )))
        (when *cbred-trace-flag*
          (trace-on))
        (values ok? goals)
        )
      )
    )
  )


;;; EOF


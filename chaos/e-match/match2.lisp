;;;-*- Mode:LISP; Package:CAFEIN; Base:10; Syntax:Common-lisp -*-
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
#|==============================================================================
                                  System:Chaos
                                 Module:e-match
                                File:match2.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; [2] Simplified versions of some matching methods for some special cases:
;;;_____________________________________________________________________________

;;; EMPTY THEORY ---------------------------------------------------------------

;;; This simplified matcher can be used for the match with a pattern which
;;; satisfies the following condition.
;;; (1) all of the operator of the pattern has no specific theory (= empty).
;;; (2) the pattern is not conditional
;;; (3) the pattern is linear and general pattern (see is-linear-general-pattern?
;;;     below).  
;;;

;;; SIMPLE-MATCH-E-OK? pattern cond
;;; returns true iff the above conditions are all satisfied.
;;;
(defun simple-match-e-ok? (pattern cond)
  (declare (type term pattern cond)
           (values (or null t)))
  (or (is-empty-theory-term? pattern)
      (and (is-true? cond)
           (is-linear-general-pattern? pattern))))

(defun is-empty-theory-term? (term)
  (declare (type term term)
           (values (or null t)))
  (if (or (term-is-variable? term)
          (term-is-builtin-constant? term))
      t
      (let ((meth (term-method term)))
        (if (or (not (= 2 (the fixnum
                            (operator-num-args (method-operator meth)))))
                (theory-info-empty-for-matching
                 (method-theory-info-for-matching meth)))
            (dolist (st (term-subterms term) t)
              (unless (is-empty-theory-term? st)
                (return nil)))
            nil))))

;;; liner & general pattern means that
;;; 1)  subterms of the pattern are all variables and their sorts
;;;     matches to the arity of the top method, and
;;; 2)  pattern is linear, i.e, no duplicated variables.
;;;
(defun is-linear-general-pattern? (pattern)
  (declare (type term pattern)
           (values (or null t)))
  (or (term-is-variable? pattern)
      ;; general pattern?
      (and
       ;; subterms of the pattern are all variables and their sorts
       ;; matches to the arity of the top method.
       (every #'(lambda (x y)
                  (declare (type term x) (type sort* y)
                           (values (or null t)))
                  (and (term-is-variable? x)
                       (sort= (variable-sort x) y)))
              (term-subterms pattern)
              (method-arity (term-method pattern)))
       ;; check linearlity
       (do* ((lst (term-subterms pattern) (cdr lst))
             (elt (car lst) (car lst)))
            ((null lst) t)
         (when (member elt (cdr lst)) (return nil))))))

;;; SIMPLE-MATCH-E : PATTERN TERM -> SUBSTITUTION NO-MATCH-FLAG
;;;-----------------------------------------------------------------------------
;;; Performs the syntactic matching. Can be used for matching to `pattern'
;;; satisfying `simple-match-e-ok?'.
;;;
;;; Conditions for matching pattern and term:
;;; (A) Case pattern is a variable:
;;;           if pattern has an substitution s1 in the current environment
;;;           pattern and term is equational equal,
;;;           else (pattern is unbound), checks sorts of these terms.
;;; (B) Case term is a variable (pattern is not a variable):
;;;           no possible matching.
;;; (C) Case pattern is built-in constant:
;;;           checks pattern and term is equal as built-in constant terms.
;;; (D) Case pattern and term are normal terms:
;;;           checks if they satisfy the following conditions:
;;;           (1) their head opertor is the same.
;;;           (2) their subterms are `simp-match*'.
;;;

;;; I'm not sure that using special variable instead passing argument really
;;; useful for effeciency, but ..
;;;
(declaim (special .empty-direct-subst.))
(defvar .empty-direct-subst. nil)       ; substitution

(defun simp-match* (pattern term)
  (declare (type term pattern term)
           (values (or null t)))
  ;; (unless term                               ; really happen this? NO!
  ;;   (return-from simp-match* (values subst nil)))
  (macrolet ((lookup-substitution (____sub _**term)
               `(cdr (assq ,_**term ,____sub))
               ;;`(let ((val (assq ,term ,sub)))
               ;;   (if val (cdr val) nil))
               ))
    (cond ((term-is-applform? pattern)
           (if (term-is-applform? term)
               (let ((head1 (term-head pattern))
                     (head2 (term-head term))
                     (subs1 (term-subterms pattern))
                     (subs2 (term-subterms term)))
                 (if (null subs1)
                     (and (null subs2)
                          (method-is-of-same-operator head1 head2))
                     (if (method-is-of-same-operator+ head1 head2)
                         (do* ((lspattern subs1 (cdr lspattern))
                               (i1 (car lspattern) (car lspattern))
                               (lsterm subs2 (cdr lsterm))
                               (i2 (car lsterm) (car lsterm)))
                              ((null lspattern) (null lsterm))
                           (declare (type list lspattern lsterm))
                           (unless (simp-match* i1 i2) (return nil)))
                         nil)))
               nil))
          ((term-is-variable? pattern)
           (let ((sl (lookup-substitution .empty-direct-subst. pattern)))
             (if sl
                 (term-equational-equal sl term)
                 (if (sort<= (term-sort term)
                             (variable-sort pattern) *current-sort-order*)
                     (progn
                       (setf .empty-direct-subst.
                             (cons (cons pattern term) .empty-direct-subst.))
                       t)
                     nil))))
          ((term-is-variable? term) nil)
          ((term-is-builtin-constant? pattern) (term-builtin-equal pattern term))
          (t nil))
    ))

(defun simp-match-e (pattern term)
  (declare (type term pattern term)
           (inline simp-match*)
           (values list list (or null t) (or null t)))
  (let ((.empty-direct-subst. nil))
    (let ((match? (simp-match* pattern term)))
      (when *match-debug*
        (with-output-simple-msg()
          (format t  "-- result : ~a" match?)))
      (values nil .empty-direct-subst. (null match?) nil))))

;;; Simplified A, AC Matching --------------------------------------------------

;;; IS-SIMPLE-AC-MATCH-OK? : pattern condition -> Bool
;;;-----------------------------------------------------------------------------
;;; checks simplified AC matching can be applied to the pattern.
;;; returns t iff the following conditions are satisfied:
;;;   (1) pattern is AC (top operator has AC theory)
;;;   (2) pattern is non conditional
;;;   (3) no duplications in idependent variables (linear).
;;; We say a variable is `independent' when it appears as a direct subterm of the
;;; pattern, and does not appear elsewhere. 
;;; Similarly, we say a non-variable is `
;;; method for unconditional non-left-linear AC rules that split into an
;;; independent and a DEPendent part
;;; Note: if the condition is successful, then the pattern is re-ordered
;;;
(defun is-simple-AC-match-ok? (pattern cond &optional (so *current-sort-order*))
  (declare (type term pattern cond)
           (type sort-order so)
           (values (or null t)))
  (block exit
    (unless (is-true? cond) (return-from exit nil)) ; must be non conditional.
    (when (term-is-variable? pattern)   ; pattern itself must be no-variable. 
      (return-from exit nil))

    (let* ((meth (term-method pattern))
           (op (method-operator meth)))
      ;; operator must be AC.
      (unless (and (operator-is-associative op) (operator-is-commutative op))
        (return-from exit nil))
      
      (let ((subs (list-AC-subterms pattern meth))
            (non-vars nil)
            (indep nil)
            (dep nil)
            (accum-vars nil)
            (top-vars nil)
            (indep-vars nil)
            (dep-vars nil)
            )

        ;; first separate out the variables.
        (dolist (tm subs)
          (if (term-is-variable? tm)
              (push tm top-vars)
              (push tm non-vars)))
        (setq non-vars (nreverse non-vars))

        ;; split non-vars into indep and dep parts.
        (let ((all-vars nil))           ;all variables contained in non-vars. 
          (dolist (nv non-vars)
            (setq all-vars (union all-vars (term-variables nv) :test #'eq)))
          (if (null all-vars)
              (setq indep non-vars
                    dep   nil)
              (let (cur)
                (while-not (subsetp all-vars accum-vars :test #'eq)
                  (setf cur (pop non-vars))
                  (push cur indep)
                  (setf accum-vars (union accum-vars (term-variables cur)
                                           :test #'eq)))
                (setf dep non-vars))))
        
        ;; split variables appearing at top level into indep and dep parts.
        (dolist (v top-vars)
          (if (member v accum-vars :test #'eq)
              (push v dep-vars)
              (if (member v indep-vars :test #'eq)
                  ;; we require linerality of independent variables.
                  (return-from exit nil)
                  (push v indep-vars))))
        (setq indep-vars (topo-sort indep-vars
                                    #'(lambda (x y)
                                        (sort< (variable-sort x)
                                               (variable-sort y)
                                               so))))
        (setq dep-vars (nreverse dep-vars))
        (if (and indep
                 (or dep                ; there are dependent or there are a few
                     dep-vars           ; easy matching cases. 
                     (< 1 (length indep-vars)))
                 (or (null (cdr indep-vars))
                                        ; indep-vars must be linearly
                                        ; ordered by sort.
                       (do ((cur (car indep-vars) nxt)
                            (nxt (cadr indep-vars) (car lst))
                            (lst (cddr indep-vars) (cdr lst)))
                           ((null nxt) t)
                         (unless (sort<= (variable-sort cur)
                                         (variable-sort nxt)
                                         so)
                           (return nil)))))
            ;; restructure the pattern.
            (progn
              (when *match-debug*
                (format t "~%is-simple-ac-match-ok?, before")
                (print-term-tree pattern)
                (format t "~%-- indep = ")
                (print-chaos-object indep)
                (format t "~%-- dep(lst) = ")
                (print-chaos-object dep)
                (format t "~%-- dep-vars = ")
                (print-chaos-object dep-vars)
                (format t "~%-- idep-vars = ")
                (print-chaos-object indep-vars)
                (force-output))
              (term-replace pattern
                            (make-right-assoc-normal-form-with-sort-check
                             meth
                             (append
                              (list (make-right-assoc-normal-form-with-sort-check
                                     meth
                                     indep))
                              dep
                              dep-vars
                              indep-vars)))
              (when *match-debug*
                (format t "~%is-simple-ac-match-ok?, after")
                (print-chaos-object pattern)
                (force-output)
                (print-term-tree pattern)
                (force-output))
              t)
            ;; else
            nil )))))


;;; DEP-MATCH : PATTERN TARGET -> GLOBALSTATE SUBSTITUTION NO-MATCH-FLAG E-EQUAL
;;;-----------------------------------------------------------------------------
;;; global state will always be nil
;;;
(defvar *match-dep-var*)

(defun dep-match (pattern t2)
  (declare (type term pattern t2)
           (values list list (or null t) (or null t)))
  (let* ((subs (term-subterms pattern))
         (indep (car subs))
         (method (term-method pattern))
         (coarity (method-coarity method))
         (new-pat (make-applform coarity method (list indep *match-dep-var*)))
         (so *current-sort-order*))
    ;;
    (multiple-value-bind (global-state subst no-match E-equal)
        (first-match new-pat t2)
      (when (or no-match E-equal)
        (return-from dep-match (values nil nil no-match E-equal)))
      (let* ((dep (list-AC-subterms (cadr subs) method))
             (dep-len (length dep)))
        (declare (type fixnum dep-len)
                 (type list dep)
                 (ignore dep-len))
        (loop 
         ;; try to finish if succeed return subst.
         (let ((ok t)
               (rest (list-AC-subterms (variable-image
                                        subst
                                        *match-dep-var*)
                                       method))
               (lst dep)
               x)
           (declare (type list rest lst))
           (when (< (the fixnum (length rest))
                    (the fixnum (length dep)))
             (return (values nil nil t nil))) ;quit whole matching process
           (block finish-match
             (while lst
               (when (null rest) (setq ok nil) (return))
               (setq x (car lst)  lst (cdr lst))
               (if (term-is-variable? x)
                   (let ((val (variable-image subst x)))
                     (if val
                         ;;remove value if find or fail; rest is not nil
                         ;;tricky point: if bound value of term has op at top
                         ;;need to treat its list-ac-subterms individually.
                         (dolist (tm (if (and (not (term-is-variable? val))
                                              (method-is-AC-restriction-of
                                               (term-head val)
                                               method))
                                         (list-AC-subterms val method)
                                         (list val)))
                           (let ((prev nil) (cur rest))
                             (loop
                              (when (null cur) (setq ok nil) (return-from finish-match))
                              (when (term-equational-equal tm (car cur))
                                (if (null prev)
                                    (setq rest (cdr rest))
                                    (rplacd prev (cdr cur)))
                                (return))
                              (setq prev cur  cur (cdr cur)))))
                         ;;else, find term for var and bind, if last done
                         (if (null lst)
                             (if (null (cdr rest))
                                 (if (sort<= (term-sort (car rest))
                                             (variable-sort x)
                                             so)
                                     (progn
                                       (push (cons x (car rest)) subst)
                                       (setq rest nil))
                                     (progn (setq ok nil) (return)))
                                 (if (sort<= coarity (variable-sort x) so)
                                     (progn
                                       (push (cons x
                                                   (make-right-assoc-normal-form-with-sort-check
                                                    method rest))
                                             subst)
                                       (setq rest nil))
                                     (progn (setq ok nil) (return))))
                             (let ((varsort (variable-sort x))
                                   (prev nil) (cur rest))
                               (loop
                                (when (null cur) (setq ok nil) (return-from finish-match))
                                (when (sort<= (term-sort (car cur)) varsort so)
                                  (if (null prev)
                                      (setq rest (cdr rest))
                                      (rplacd prev (cdr cur)))
                                  (push (cons x (car cur)) subst)
                                  (return))
                                (setq prev cur  cur (cdr cur))))
                             )))
                   ;; instantiate and find or fail; rest is not nil
                   (let ((instx (substitution-image subst x))
                         (prev nil) (cur rest))
                     (loop
                      (when (null cur) (setq ok nil) (return-from finish-match))
                      (when (term-equational-equal instx (car cur))
                        (if (null prev)
                            (setq rest (cdr rest))
                            (rplacd prev (cdr cur)))
                        (return))
                      (setq prev cur  cur (cdr cur)))))
               ))                       ; finish-match ----------
           (when (and ok (null rest)) (return (values nil subst nil nil))))
         ;;
         (multiple-value-setq (global-state subst no-match)
           (next-match global-state))
         (when no-match
           (return (values nil nil t nil)))) ; loop --------------------------
        ;;
        ))))

;;; MATCH-DEP-WITH-THEORY : theory pattern target
;;;                             -> global-state substitution no-match-flag e-equal
;;;-----------------------------------------------------------------------------
;;; want this for id-A and id-AC variants
;;; should try and integrate with the above code.
;;; note: next-match uses the theory already determined.
;;;

(defun match-dep-with-theory (theory t1 t2)
  (declare (type theory-info theory)
           (type term t1 t2))
  (let* ((subs (term-subterms t1))
         (indep (car subs))
         (meth (term-head t1))
         (coar (method-coarity meth))
         (newpat (make-applform coar meth (list indep *match-dep-var*))))
    (declare (type list subs))
    (multiple-value-bind
          (global-state subst no-match E-equal)
        (first-match-with-theory theory newpat t2)
      (if (or no-match E-equal)
          (values nil nil no-match E-equal)
          (let ((dep (list-AC-subterms (cadr subs) meth))
                (so *current-sort-order*))
            (declare (type list dep)
                     (type sort-order so))
            (loop
             ;; try to finish if succeed return subst.
             (let ((ok t)
                   (rest (list-AC-subterms (variable-image
                                            subst
                                            *match-dep-var*)
                                           meth))
                   (lst dep)
                   x)
               (declare (type list rest))
               (when (< (length rest) (length dep))
                 (return (values nil nil t nil))) ; quit whole matching process
               (block finish-match
                 (loop
                  (when (null lst) (return))
                  (when (null rest) (setq ok nil) (return))
                  (setq x (car lst)
                        lst (cdr lst))
                  (if (term-is-variable? x)
                      (let ((val (variable-image subst x)))
                        (if val
                            ;; remove value if find or fail; rest is not nil
                            ;; tricky point: if bound value of term has op at top
                            ;;  need to treat its term-list-ac-subterms individually
                            (dolist (tm (if (and (not (term-is-applform? val))
                                                 (method-is-AC-restriction-of
                                                  (term-head val)
                                                  meth))
                                            (list-AC-subterms val meth)
                                            (list val)))
                              (let ((prev nil)
                                    (cur rest))
                                (loop
                                 (when (null cur)
                                   (setq ok nil)
                                   (return-from finish-match))
                                 (when (term-equational-equal tm (car cur))
                                   (if (null prev)
                                       (setq rest (cdr rest))
                                       (rplacd prev (cdr cur)))
                                   (return))
                                 (setq prev cur  cur (cdr cur)))))
                            ;; find term for var and bind; if last done
                            (if (null lst)
                                (if (null (cdr rest))
                                    (if (sort<= (term-sort (car rest))
                                                (variable-sort x)
                                                so)
                                        (progn (push (cons x (car rest)) subst)
                                               (setq rest nil))
                                        (progn (setq ok nil)
                                               (return)))
                                    (if (sort<= coar (variable-sort x) so)
                                        (progn
                                          (push
                                           (cons x
                                                 (make-right-assoc-normal-form-with-sort-check
                                                  meth rest))
                                           subst)
                                          (setq rest nil))
                                        (progn (setq ok nil)
                                               (return))))
                                (let ((varsort (variable-sort x))
                                      (prev nil)
                                      (cur rest))
                                  (loop
                                   (when (null cur)
                                     (setq ok nil)
                                     (return-from finish-match))
                                   (when (sort<= (term-sort (car cur))
                                                 varsort
                                                 so)
                                     (if (null prev)
                                         (setq rest (cdr rest))
                                         (rplacd prev (cdr cur)))
                                     (push (cons x (car cur)) subst)
                                     (return))
                                   (setq prev cur
                                         cur (cdr cur))
                                   )))))
                      ;; instantiate and find or fail; rest is not nil
                      (let ((instx (substitution-image subst x))
                            (prev nil)
                            (cur rest))
                        (loop (when (null cur)
                                (setq ok nil)
                                (return-from finish-match))
                              (when (term-equational-equal instx (car cur))
                                (if (null prev)
                                    (setq rest (cdr rest))
                                    (rplacd prev (cdr cur)))
                                (return))
                              (setq prev cur
                                    cur (cdr cur)))))
                  ))                    ; -- block finish-match
               (when (and ok (null rest))
                 (return (values nil subst nil nil))))
             ;; 
             (multiple-value-setq (global-state subst no-match)
               (next-match global-state))
             (when no-match
               (return (values nil nil t nil)))
             ))))))


;;; IDEMPOTENT ---------------------------------------------------------------
;;; case:  X + X = X
;;; 
(defun match-is-idem-ok? (lhs cond kind)
  (declare (ignore lhs cond))
  (eq kind :idem-theory))

(defun match-is-idem-ok2? (lhs cond kind)
  (declare (ignore kind))
  (and (is-true? cond)
       (not (term-is-variable? lhs))
       (not (term-is-builtin-constant? lhs))
       (let ((method (term-head lhs)))
         (and (method-is-associative method)
              (method-is-commutative method)
              (method-is-idempotent method)
              (let* ((arity (method-arity method))
                     (subs (term-subterms lhs))
                     (sub-1 (car subs))
                     (sub-2 (cadr subs)))
                (and (term-is-variable? sub-1)
                     ;; (term-is-variable? sub-2) ; this is redundant.
                     (eq sub-1 sub-2)
                     (sort= (variable-sort sub-1) (car arity))
                     (sort= (variable-sort sub-2) (cadr arity))))))))

;;; NOTE: assume that the rules is actually created in the form e + (x + x).
;;;
(defun match-is-idem-ext-ok? (lhs cond kind)
  (declare (type term lhs cond)
           (values (or null t)))
  (and (is-true? cond)
       (not (term-is-variable? lhs))
       (let ((method (term-head lhs)))
         (and (method-is-associative method)
              (method-is-commutative method)
              (method-is-idempotent method)
              (let* ((arity (method-arity method))
                     (subs (term-subterms lhs))
                     (sub-1 (car subs))
                     (sub-2 (cadr subs)))
                (and (term-is-variable? sub-1)
                     (let ((vs (variable-sort sub-1)))
                       (or (or (sort= vs *universal-sort*)
                               (sort= vs *huniversal-sort*)
                               (sort= vs *cosmos*))
                           (and (sort= vs (car arity))
                                (sort= vs (cadr arity)))))
                     (match-is-idem-ok2? sub-2 cond kind)
                     (not (eq sub-1 (car (term-subterms sub-2)))) 
                     ))))))

;;; EOF

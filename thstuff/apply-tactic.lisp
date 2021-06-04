;;;-*-Mode:LISP; Package: CHAOS; Base:10; Syntax:Common-lisp -*-
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
                                   Module:thstuff
                                File:apply-tactic.lisp
 =============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; ****************************************************************************
;;; UTILITIES
;;; ****************************************************************************

;;; distribute-sentences : ptree-node List(axiom) -> List(goal)
;;; if there are multiple sentences, distribute them into newly genereted goals for each
;;;
(defun distribute-sentences (parent axioms tactic)
  (declare (type ptree-node parent))
  (let ((new-goals nil)
        (goal nil))
    (cond ((cdr axioms)
           (dolist (ax axioms)
             (setq goal (prepare-next-goal parent tactic))
             (setf (goal-targets goal) (list ax))
             (push goal new-goals)))
          (t (push (ptree-node-goal parent) new-goals)))
    (nreverse new-goals)))

;;; rule-copy-canonicalized : rule module -> rule
;;; copy rule with all variables are renewed and noralized.
;;;
(defun remove-nonexec (rule)
  (let ((l nil))
    (dolist (lb (rule-labels rule))
      (unless (member lb non-exec-labels)
        (push lb l)))
    (setf (rule-labels rule) (nreverse l))
    (setf (rule-non-exec rule) nil)
    rule))

(defun rule-copy-canonicalized (rule module &optional labels remove-non-exec)
  (with-in-module (module)
    (let* ((new-rule (if remove-non-exec
                         (remove-nonexec (rule-copy rule))
                       (rule-copy rule)))
           (canon (canonicalize-variables (list (rule-lhs new-rule)
                                                (rule-rhs new-rule)
                                                (rule-condition new-rule))
                                          module)))
      (setf (rule-lhs new-rule) (first canon)
            (rule-rhs new-rule) (second canon)
            (rule-condition new-rule) (third canon))
      (when labels
        (setf (rule-labels new-rule) (append (rule-labels rule) labels)))
      new-rule)))

;;; apply-substitution-to-axiom : subst axiom [label] [add] -> axiom'
;;;
(defun apply-substitution-to-axiom (subst axiom &optional label add)
  (setf (rule-lhs axiom) (substitution-image-simplifying subst (rule-lhs axiom))
        (rule-rhs axiom) (substitution-image-simplifying subst (rule-rhs axiom))
        (rule-condition axiom) (if (is-true? (rule-condition axiom))
                                   *bool-true*
                                 (substitution-image-simplifying subst (rule-condition axiom))))
  (when (and label (atom label))
    (setf label (list label)))
  (let ((new-label (if add
                       (append label
                               (rule-labels axiom))
                     ;; overwrite, but preserves :nonexec
                     (if (axiom-non-exec axiom)
                         (append label (list '|:nonexec|))
                       label))))
    (setf (rule-labels axiom) new-label)
    axiom))

;;; copy-constant-term
;;;
(defun copy-constant-term (constant)
  (make-applform (term-sort constant) (term-head constant) nil))

;;; select-comb-elems : List(List) -> List
;;; 
(defun select-combs-aux (max-idx list-of-list)
  (declare (type fixnum max-idx)
           (type list list-of-list))
  (let* ((result nil)
         (target (car list-of-list))
         (rest (cdr list-of-list))
         (len (length target)))
    (declare (type fixnum len)
             (type list result target rest))
    (if target
        (let ((idx 0))
          (declare (type fixnum idx))
          (while (< idx max-idx)
            (let ((elt (nth (mod idx len) target))
                  (rr (select-combs-aux max-idx rest)))
              (if rr
                  (dolist (r rr)
                    (pushnew (cons elt r) result :test #'equal))
                (pushnew (list elt) result :test #'equal))
              (incf idx)))
          (nreverse result))
      nil)))

(defun select-combs-aux-indexed (max-idx list-of-list index)
  (declare (type fixnum max-idx index)
           (type list list-of-list))
  (let* ((result nil)
         (target (car list-of-list))
         (rest (cdr list-of-list))
         (len (length target)))
    (declare (type fixnum len)
             (type list result target rest))
    (if target
        (let ((idx 0))
          (declare (type fixnum idx))
          (while (< idx max-idx)
            (let ((elt (nth (mod idx len) target))
                  (rr (select-combs-aux-indexed max-idx rest (1+ index))))
              (if rr
                  (dolist (r rr)
                    (pushnew (cons (cons index elt) r) result :test #'equal))
                (pushnew (list (cons index elt)) result :test #'equal))
              (incf idx)))
          (nreverse result))
      nil)))

(defun select-comb-elems (list-of-list &optional (indexed nil))
  (declare (type list list-of-list))
  (unless list-of-list (return-from select-comb-elems nil))
  (let ((max-idx (apply #'max (mapcar #'(lambda (x) (length x)) list-of-list))))
    (declare (type fixnum max-idx))
    (if indexed
        (select-combs-aux-indexed max-idx list-of-list 0)
      (select-combs-aux max-idx list-of-list))))

;;; axiom-variables : axiom -> List(variable)
;;; returns a list of variables contained in the given axiom
;;;
(defun axiom-variables (ax)
  (let ((lhs (axiom-lhs ax))
        (rhs (axiom-rhs ax))
        (cond (axiom-condition ax))
        (result nil))
    (declare (type list result))
    (setq result (append (term-variables lhs)
                         (append (term-variables rhs)
                                 (term-variables cond))))
    (delete-duplicates result :test #'variable-equal)))

;;; normalize-term-in : module term -> term Bool
;;; reduces the ground terms in given term by rewriting.
;;; if rewritten, returned term is distructively changed.
;;;
(defun normalize-term-in (module term &optional (reduction-mode :red) var-is-const)
  (let ((applied? nil)
        (rule-count-save (number-rewritings))
        (*variable-as-constant* var-is-const))
    (declare (type fixnum rule-count-save)
             (optimize (speed 3) (safety 0)))
    (reducer-no-stat term module reduction-mode)
    (unless (= rule-count-save (the fixnum (number-rewritings)))
      (setq applied? t))
    (values term applied?)))

;;; normalize-sentence : axiom module -> axiom' Bool
;;; normalize an axiom by reduction, returns the result.
;;; NOTE: given axiom is preserved (not changed).
;;;
(defun normalize-sentence (ax module &optional lhs-only variable-is-constant)
  (declare (type rewrite-rule ax)
           (type module module)
           (type (or null t) lhs-only variable-is-constant)
           (optimize (speed 3) (safety 0)))
  (if-spoiler-on 
   ;; normalize sentence only if :spoiler is on
   :then (let ((target (rule-copy-canonicalized ax module)))
           (with-in-module (module)
             (let ((lhs (rule-lhs target))
                   (rhs (rule-rhs target))
                   (condition (rule-condition target))
                   (reduction-mode (if (eq (rule-type ax) :equation)
                                       :red
                                     :exec))
                   (applied nil)
                   (app? nil))
               (flet ((set-applied (val)
                        (or app? (setq app? val))))
                 (with-citp-debug ()
                   (with-in-module (module)
                     (format t "~%[NF] target:")
                     (print-next)
                     (print-axiom-brief target)))
                 (let ((rsubst nil))
                   ;; variables->pconst if requred
                   (when variable-is-constant
                     (setq rsubst (nconc (variables->pconstants lhs)
                                         (nconc (variables->pconstants rhs)
                                                (variables->pconstants condition)))))
                   ;; normalize lhs
                   (multiple-value-setq (lhs applied)
                     (normalize-term-in module (reset-reduced-flag lhs) :red))
                   (set-applied applied)
                   (when (eq reduction-mode :exec)
                     (multiple-value-setq (lhs applied) 
                       (normalize-term-in module (reset-reduced-flag lhs) :exec))
                     (set-applied applied))
                   ;; normalize rhs
                   (unless lhs-only
                     (multiple-value-setq (rhs applied) 
                       (normalize-term-in module (reset-reduced-flag rhs)))
                     (set-applied applied))
                   ;; normalize condition
                   (unless (or lhs-only (is-true? condition))
                     (multiple-value-setq (condition applied)
                       (normalize-term-in module (reset-reduced-flag condition) :red))
                     (set-applied  applied))
                   ;; pconsts -> variables
                   (when rsubst
                     (revert-pconstants lhs rsubst)
                     (revert-pconstants rhs rsubst)
                     (revert-pconstants condition rsubst))
                   (setf (rule-lhs target) lhs)
                   (setf (rule-rhs target) rhs)
                   (setf (rule-condition target) condition)
                   (with-citp-debug ()
                     (if (not app?)
                         (format t "~%    ...not applied: ")
                       (progn
                         (print-next)
                         (princ "==> ") (print-axiom-brief target))))
                   (return-from normalize-sentence (values target app?)))))))
   ;; do nothing if :spoiler is off
   :else (values ax nil)))

;;; is-contradiction : term term -> Bool
;;; returns true if true ~ false, or false ~ true
;;;
(defun is-contradiction (t1 t2)
  (declare (ignore t1 t2))
  nil)

;;; sentence-is-satisfied : axiom module -> { :satisfied | :ct | nil }
;;;
(defun sentence-is-satisfied (sentence module)
  (let ((old-condition (rule-condition sentence)))
    (multiple-value-bind (norm-sen app?)
        (normalize-sentence sentence module)
      (declare (ignore app?))
      (let ((lhs (rule-lhs norm-sen))
            (rhs (rule-rhs norm-sen))
            (condition (rule-condition norm-sen))
            (result nil))
        (with-citp-debug ()
          (format t "~%[satisfied?]: ")
          (print-axiom-brief norm-sen))
        (cond ((and (not (is-true? old-condition)) (is-true? condition))
               (if (is-contradiction lhs rhs)
                   (setq result :ct)
                 (setq result :st)))
              ((is-true? condition)     ; originally the axiom was non-conditional
               (if (is-contradiction lhs rhs)
                   (setq result :ct)
                 (let ((x-lhs (normalize-term-in module (reset-reduced-flag lhs)))
                       (x-rhs (normalize-term-in module (reset-reduced-flag rhs))))
                   (when (term-equational-equal x-lhs x-rhs)
                     (setq result :st)))))
              (t (setq result nil)))
        (with-citp-debug ()
          (format t "~% --> ~a: " result)
          (print-next)
          (print-axiom-brief norm-sen))
        (values result norm-sen)))))

;;; check-contradiction : goal -> Bool
;;; check if 
;;; * 'true => false' or 
;;; * 'false => true' or
;;; * (t = t) = false 
(defun check-true<=>false (module &optional (report-header nil))
  (with-in-module (module)
    (let ((t-rules (method-rules-with-different-top *bool-true-meth*))
          (f-rules (method-rules-with-different-top *bool-false-meth*))
          (ct-rule nil))
      (dolist (rule (append t-rules f-rules))
        (with-citp-debug ()
          (format t "~%check true<=> false")
          (print-next)
          (print-axiom-brief rule))
        (when (or (is-true? (rule-condition rule))
                  (is-true? (normalize-term-in module
                                               (reset-reduced-flag (term-copy-and-returns-list-variables
                                                                    (rule-condition rule))))))
          (unless (term-equational-equal (rule-lhs rule) (rule-rhs rule))
            (setq ct-rule rule)
            (with-citp-debug ()
              (format t "~% CT found!"))
            (return nil))))
      (when (and ct-rule report-header)
        (format t "~%[~a] contradiction: " report-header)
        (let ((*print-indent* (+ 2 *print-indent*)))
          (print-next)
          (print-axiom-brief ct-rule)))
      ct-rule)))

(defun check-contradictory-assumptions (goal &optional (report-header nil))
  (let ((ams (goal-assumptions goal))
        (contra? nil))
    (with-in-module ((goal-context goal))
      (dolist (ax ams)
        (when (and (is-true? (rule-condition ax))
                   (or (and (is-false? (rule-rhs ax))
                            (is-true? (rule-lhs ax)))
                       (and (is-false? (rule-lhs ax))
                            (is-true? (rule-rhs ax)))))
          (when report-header
            (format t "~%[~a] contradictory assumption: " report-header)
            (print-next)
            (print-axiom-brief ax))
          (setf contra? t)))
      contra?)))

(defun check-contradiction (goal &optional (report-header nil))
  (let ((module (goal-context goal)))
    (or (check-true<=>false module report-header)
        (check-contradictory-assumptions goal report-header)
        (with-in-module (module)
          (let ((true-term (make-applform *bool-sort* *bool-true-meth* nil))
                (false-term (make-applform *bool-sort* *bool-false-meth* nil)))
          (let ((true=false (make-applform *bool-sort* *eql-op* (list true-term false-term))))
            (multiple-value-bind (t-result t-applied?)
                (normalize-term-in module true=false)
              (when (and t-applied? (is-true? t-result))
                (when report-header
                  (format t "~%[~a] contradiction: " report-header)
                  (print-next)
                  (format t "  `true = false' can be derived!"))
                (return-from check-contradiction t))))))
      nil)))

;;; check-le : goal -> goal'
;;;
(defun check-le (goal)
  (let ((mod (goal-context goal)))
    (with-in-module (mod)
      (let ((axs (module-equations mod))
            (ls-pats nil)
            (le-pats nil))
        (dolist (ax axs)
          (block next
            (unless (is-true? (rule-condition ax)) (return-from next))
            (when (axiom-variables ax) (return-from next))
            (let ((lhs (rule-lhs ax)))
              (multiple-value-bind (match? subst)
                  (@pat-match .ls-pat. lhs)
                (cond (match? (push (cons (term-arg-1 lhs) (term-arg-2 lhs)) ls-pats))
                      (t (multiple-value-setq (match? subst)
                           (@pat-match .le-pat. lhs))
                         (when match? (push (cons (term-arg-1 lhs) (term-arg-2 lhs)) le-pats))))))))
        (let ((ls-r nil)
              (le-r nil))
          (dolist (ls ls-pats)
            (let ((ls-pair (find (cdr ls) ls-pats :key #'car :test #'term-equational-equal))
                  (le-pair (find (cdr ls) le-pats :key #'car :test #'term-equational-equal)))
              ;; G1 < G2 < G3 
              (when ls-pair (push (cons (car ls) (cdr ls-pair)) ls-r)) ; < check G3 < G1
              ;; G1 < G2 <= G3
              (when le-pair (push (cons (car ls) (cdr le-pair)) le-r)))) ; <= check G3 <= G1
          (dolist (le le-pats)
            (let ((ls-pair (find (cdr le) ls-pats :key #'car :test #'term-equational-equal))
                  (le-pair (find (cdr le) le-pats :key #'car :test #'term-equational-equal)))
              ;; G1 <= G2 < G3
              (when ls-pair (push (cons (car le) (cdr ls-pair)) le-r)) ; check G3 <= G1
              (when le-pair (push (cons (car le) (cdr le-pair)) ls-r)))) ; check G3 < G1
          ;;
          (with-citp-debug ()
            (format t "~%[le] check in goal ~s: " (goal-name goal))
            (dolist (ls ls-r)
              (print-next)
              (term-print (cdr ls)) (princ " < ")
              (term-print (car ls)))
            (dolist (le le-r)
              (print-next)
              (term-print (cdr le)) (princ " <= ")
              (term-print (car le))))
          (flet ((do-check (pat op)
                   (dolist (ls pat)
                     (let ((rg (make-applform *bool-sort* 
                                              op
                                              (list (cdr ls) (car ls)))))
                       (with-citp-debug ()
                         (format t "~% target term : ")
                         (term-print-with-sort rg))
                       (when (is-true? (normalize-term-in *current-module* rg))
                         ;; discharge the goal
                         (let ((target (rule-copy-canonicalized (car (goal-targets goal))
                                                                *current-module*)))
                           (setf (rule-labels target) (cons 'le (rule-labels target)))
                           (setf (goal-targets goal) nil)
                           (setf (goal-proved goal) (list target))
                           (format t "~%[le] discharged the goal ~s" (goal-name goal)))
                         (return nil))))))
            (do-check ls-r (term-head .ls-pat.))
            (do-check le-r (term-head .le-pat.))))))))

;;; make-new-assumption : module lhs rhs -> new-lhs new-rhs axiom-type
;;;
(defun boolean-constant? (term)
  (or (is-true? term)(is-false? term)))

(defun is-builtin= (op)
  (or (method= *eql-op* op)
      (memq *eql-op* (method-overloaded-methods op))))

(defun simplify-boolean-axiom (lhs rhs)
  (let ((r-lhs lhs)
        (r-rhs rhs)
        (type :equation))
    (with-citp-debug ()
      (format t "~%== simplify: ")
      (format t "~% lhs = ")(term-print-with-sort lhs)
      (format t "~% rhs = ")(term-print-with-sort rhs))
    (cond ((is-builtin= (term-head lhs))
           (with-citp-debug ()
             (format t "~%** case _=_"))
           ;; (T1 = T2) = true/false  ==> T1 = T2
           (let* ((arg1 (term-arg-1 lhs))
                  (arg2 (term-arg-2 lhs))
                  (arg1-is-bconstant (boolean-constant? arg1))
                  (arg2-is-bconstant (boolean-constant? arg2)))
             (cond ((is-true? rhs)
                    (with-citp-debug ()
                      (format t "~%-- (T1 = T2) = true"))
                    ;; (T1 = T2) = true
                    (cond ((term-equational-equal arg1 arg2)
                           ;; (T1 = T1) = true : dangerous tautology
                           (with-citp-debug ()
                             (format t "~%-- (T = T) = true, tautology."))
                           (let ((*chaos-quiet* nil))
                             (with-output-chaos-warning ()
                               (format t "Found the new assumption is tautology:")
                               (print-next)
                               (format t "LHS: ") (term-print-with-sort arg1)
                               (print-next)
                               (format t "RHS: ") (term-print-with-sort arg2)
                               (format t "~%... ignored.")))
                           (setf r-lhs nil
                                 r-rhs nil))
                          ((and arg1-is-bconstant arg2-is-bconstant)
                           (with-citp-debug ()
                             (format t "~%-- (true = false) = true, (false = true) = true."))
                           ;; (true = false), (false = true) = true .
                           ;; contradiction
                           (setf r-lhs arg1
                                 r-rhs arg2)
                           (let ((*print-indent* (+ 2 *print-indent*)))
                             (let ((*chaos-quiet* nil))
                               (with-output-chaos-warning ()
                                 (format t "Caution!, you are introducing contradiction:")
                                 (print-next)
                                 (format t "LHS: ") (term-print-with-sort r-lhs)
                                 (print-next)
                                 (format t "RHS: ") (term-print-with-sort r-rhs)))))
                          (t 
                           ;; (T1 = T2) = true --> T1 = T2
                           (with-citp-debug ()
                             (format t "~% trying to simplify.."))
                           (setf r-lhs (if arg1-is-bconstant
                                             arg2
                                           arg1))
                           (setf r-rhs (if arg1-is-bconstant
                                           arg1
                                         arg2)))))
                   ((is-false? rhs)
                    ;; (T1 = T2) = false
                    (with-citp-debug ()
                      (format t "~%-- (T1 = T2) = false"))
                    (cond ((term-equational-equal arg1 arg2)
                           ;; (T = T) = false 
                           ;; contradiction
                           (with-citp-debug ()
                             (format t "~%  (T = T) = false, contradiction!"))
                           (let ((*print-indent* (+ 2 *print-indent*))
                                 (*chaos-quiet* nil))
                             (with-output-chaos-warning ()
                               (format t "Caution! you are introducing contradiction:")
                               (print-next)
                               (format t "LHS: ") (term-print-with-sort lhs)
                               (print-next)
                               (format t "RHS: ") (term-print-with-sort rhs))))
                          ((and arg1-is-bconstant arg2-is-bconstant)
                           ;; (true = false) = false, (false = true) = false
                           (with-citp-debug ()
                             (format t "~%(true = false) = false, (false = true) = false"))
                           (let ((*print-indent* (+ 2 *print-indent*))
                                 (*chaos-quiet* nil))
                             (with-output-chaos-warning ()
                               (format t "Redundant assumption: ")
                               (print-next)
                               (format t "LHS: ") (term-print-with-sort lhs)
                               (print-next)
                               (format t "RHS: ") (term-print-with-sort rhs))
                             (format t "~%... ignored."))
                           (setf r-lhs nil
                                 r-rhs nil))
                          (t 
                           ;;
                           (with-citp-debug ()
                             (format t "-- trying to simplify.."))
                           (if (is-true? arg1)
                                 (setf r-lhs arg2
                                       r-rhs *bool-false*)
                               (if (is-true? arg2)
                                   (setf r-lhs arg1
                                         r-rhs *bool-false*)
                                 (if (is-false? arg1)
                                     (setf r-lhs arg2
                                           r-rhs *bool-true*)
                                   (if (is-false? arg2)
                                       (setf r-lhs arg1
                                             r-rhs *bool-true*)
                                     (setf r-lhs lhs
                                           r-rhs rhs)))))))))))
          ((method= *bool-match* (term-head lhs))
           ;; (T1 := T2) = true  ==> T2 = T1
           (setf r-lhs (term-arg-2 lhs)
                 r-rhs (term-arg-1 lhs)))
          ((method= *rwl-predicate* (term-head lhs))
           ;; (T1 => T2) = true ==> T1 => T2
           (setf r-lhs (term-arg-1 lhs)
                 r-rhs (term-arg-2 lhs))
           (setq type :rule)))
    
    (with-citp-debug ()
      (when r-lhs
        (format t "~%=> ")
        (format t "~%LHS: ")(term-print-with-sort r-lhs)
        (format t "~%RHS: ")(term-print-with-sort r-rhs)
        (format t "~%type: ~a" type)))
    (if r-lhs
        (values r-lhs r-rhs type)
      (values nil nil nil))))
    
(defun make-new-assumption (module lhs &optional (label-prefix nil))
  (with-in-module (module)
    (let ((r-lhs lhs)
          (r-rhs *bool-true*)
          (type :equation))
      (when (is-builtin= (term-head lhs))
        ;; (T1 = T2) = true  ==> T1 = T2
        (setf r-lhs (term-arg-1 lhs)
              r-rhs (term-arg-2 lhs)))
      (when (method= *bool-match* (term-head lhs))
        ;; (T1 := T2) = true  ==> T2 = T1
        (setf r-lhs (term-arg-2 lhs)
              r-rhs (term-arg-1 lhs)))
      (when (method= *rwl-predicate* (term-head lhs))
        ;; (T1 => T2) = true ==> T1 => T2
        (setf r-lhs (term-arg-1 lhs)
              r-rhs (term-arg-2 lhs))
        (setq type :rule))
      (compile-module module)
      (let ((axiom (make-rule :lhs (normalize-term-in module (reset-reduced-flag r-lhs))
                              :rhs (normalize-term-in module (reset-reduced-flag r-rhs))
                              :condition *bool-true*
                              :type type
                              :behavioural nil
                              :labels (if label-prefix (list label-prefix) nil))))
        ;; check tautology
        (when (term-equational-equal r-lhs r-rhs)
          (return-from make-new-assumption nil))
        (with-citp-debug ()
          (format t "~%** new assumption: ")
          (print-axiom-brief axiom))
        axiom))))

;;; condition->axioms : module term -> List(axiom)
;;;
(defun condition->axioms (module condition &optional (rule-label nil))
  (with-in-module (module)
    (let ((axs nil)
          (cps nil))
      (if (method= *bool-cond-op* (term-head condition))
          (let ((subs (list-assoc-subterms condition *bool-cond-op*)))
            (dolist (sub subs)
              (push (term-copy-and-returns-list-variables sub) cps)))
        (setq cps (list (term-copy-and-returns-list-variables condition))))
      (dolist (c cps)
        (let ((new-ax (make-new-assumption module c rule-label)))
          (when new-ax
            (compute-rule-method new-ax)
            (pushnew new-ax axs :test #'rule-is-similar?))))
      (with-citp-debug ()
        (format t "~%[~a] generated axioms:" rule-label)
        (dolist (ax axs)
          (print-next)
          (print-axiom-brief ax)))
      axs)))

(defun axiom-is-an-instance-of (ax cx module)
  (with-in-module (module)
    (with-citp-debug ()
      (print-next)
      (format t "* ax: ") (print-axiom-brief ax)
      (print-next)
      (format t "* cx: ") (print-axiom-brief cx))
    (multiple-value-bind (gs subst no-match E-equal)
        (funcall (rule-first-match-method cx) (rule-lhs cx) (rule-lhs ax))
      (when no-match (return-from axiom-is-an-instance-of nil))
      (when e-equal (setq subst nil))
      (let ((pat-instance (substitution-image-simplifying subst (rule-rhs cx)))
            (t-instance (rule-rhs ax))
            (next-match-method nil))
        (with-citp-debug ()
          (format t "~%* matched: ")
          (print-substitution subst)
          (print-next)
          (format t "pat: ") (term-print-with-sort pat-instance)
          (print-next)
          (format t "rhs: ") (term-print-with-sort t-instance))

        (when (term-equational-equal t-instance pat-instance)
          (return-from axiom-is-an-instance-of t))
        ;; try other match
        (setq next-match-method (rule-next-match-method cx))
        (loop
          (multiple-value-setq (gs subst no-match)
            (funcall next-match-method gs))
          (when no-match (return-from axiom-is-an-instance-of nil))
          (setq pat-instance (substitution-image-simplifying subst (rule-rhs cx)))
          (when (term-equational-equal t-instance pat-instance)
            (return-from axiom-is-an-instance-of t))))
      nil)))

(defun check-ct-with-axioms (goal axioms &optional report-header)
    (declare (type goal goal)
             (type list axioms))
    (with-in-module ((goal-context goal))
      (let ((tf-rules (append (method-rules-with-different-top *bool-true-meth*)
                              (method-rules-with-different-top *bool-false-meth*))))
        ;; first do light weight check
        (dolist (rule tf-rules)
          (when (is-true? (rule-condition rule))
            ;; already CT
            (when report-header
              (format t "~%[~a] found contradiction: " report-header)
              (print-axiom-brief rule))
            (return-from check-ct-with-axioms :ct)))
        (dolist (rule tf-rules)
          (let ((cond-axioms (condition->axioms *current-module* (rule-condition rule))))
            (let ((remaining cond-axioms))
              (do* ((cax (car remaining) (car remaining))
                    (axs axioms (cdr axs))
                    (ax (car axs) (car axs)))
                  ((or (null cax) (null axs)))
                (when (axiom-is-an-instance-of ax cax *current-module*)
                  (setq remaining (remove cax remaining))))
              (unless remaining
                (when report-header
                  (format t "~%[~a] found contradiction: " report-header)
                  (print-axiom-brief rule))
                (return-from check-ct-with-axioms :ct)))))
        nil)))

;;; check-sentence&mark-label : sentence module -> (<result> <normalized-sentence> <origina-sentence>)
;;; 
(defun check-sentence&mark-label (sentence goal &optional (report-header nil))
  (flet ((make-st-label ()
           (let ((lbl (or report-header 'st)))
             (cons lbl (rule-labels sentence))))
         (make-ct-label ()
           (let ((lbl (if report-header
                          (intern (format nil "CT-~A" report-header))
                        'ct)))
             (cons lbl (rule-labels sentence))))
         (make-ic-label ()
           (let ((lbl (if report-header
                          (intern (format nil "IC-~A" report-header))
                        'ic)))
             (cons lbl (rule-labels sentence)))))
    ;;
    (let ((module (goal-context goal)))
      (with-in-module (module)
        (let ((target sentence)
              (res nil)
              (*print-indent* (+ 2 *print-indent*))
              (*print-line-limit* 80)
              (*print-xmode* *print-xmode*))
          (if (check-contradiction goal report-header)
              (setq res :ct)
            (multiple-value-setq (res target)
              (sentence-is-satisfied sentence module)))
          (when res
            ;; discharged by certain reson
            (setq sentence (rule-copy-canonicalized sentence *current-module*)))
          (with-in-module (module)
            ;; check how did we did dischage
            (case res
              (:st (when report-header
                     (format t "~%[~a] discharged: " report-header)
                     (print-next)
                     (print-axiom-brief sentence))
                   (setf (rule-labels sentence) (make-st-label))
                   (values :st target sentence))
              (:ct (when report-header
                     (format t "~%[~a] discharged: " report-header)
                     (print-next)
                     (print-axiom-brief sentence))
                   (setf (rule-labels sentence) (make-ct-label))
                   (values :ct target sentence))
              (:ic (when report-header
                     (format t "~%[~a] discharged: " report-header)
                     (print-next)
                     (print-axiom-brief sentence))
                   (setf (rule-labels sentence) (make-ic-label))
                   (values :ic target sentence))
              ;; could not discharge
              (otherwise (values nil target sentence)))))))))

;;; set-operator-rewrite-rule : module axiom -> void
;;;
(defun set-operator-rewrite-rule (module axiom)
  (check-axiom-validity axiom module)
  (when (and (not (axiom-non-exec axiom))
             (term-is-applform? (rule-lhs axiom)))
    (add-rule-to-method axiom (term-head (rule-lhs axiom)) (module-opinfo-table module))))

;;; add-assumptions-to-goal : goal assumptions -> void
;;;
(defun add-assumptions-to-goal (goal assumptions)
  (let ((module (goal-context goal)))
    (with-in-module (module)
      (dolist (ax assumptions)
        (adjoin-axiom-to-module module ax)
        (set-operator-rewrite-rule module ax))
      (compile-module module t))))

;;; check-goal-is-satisfied : goal -> ( <result> <normalized-target> <possibly-marked-target> )
;;;
(defun check-goal-is-satisfied (goal &optional (report-header nil))
  (when (cdr (goal-targets goal))
    (with-output-chaos-error ('invalid-proof-seq)
      (format t "Internal error. more than one target!")))
  (if-spoiler-on
   :then (let ((target (car (goal-targets goal))))
           (multiple-value-bind (discharged normalized-target original-target)
               (do-check-sentence target goal report-header)
             (when discharged
               (setf (goal-targets goal) nil
                     (goal-proved goal) (list original-target)))
             (values discharged normalized-target original-target)))
   :else (values nil nil (car (goal-targets goal)))))

(defun make= (lhs rhs mod)
  (let ((eq-form (make-applform *bool-sort*
                                *eql-op* ; _=_
                                (list lhs rhs))))
    (with-in-module (mod)
      (update-lowest-parse eq-form))))

(defun do-check-sentence (target goal &optional report-header)
  (let ((mod (goal-context goal)))
    (multiple-value-bind (result norm-target marked-target)
        (check-sentence&mark-label target goal report-header)
      (cond (result
             ;; goal has been dischared already by some reason
             )
            ((and (is-true? (rule-condition target))
                  (eq (rule-type target) :equation))
             (setf target (rule-copy-canonicalized target mod))
             (setf (rule-lhs target) (make= (rule-lhs target) (rule-rhs target) mod)
                   (rule-rhs target) *bool-true*)
             (multiple-value-bind (res-2 norm-target-2 marked-target-2)
                 (check-sentence&mark-label target goal report-header)
               (declare (ignore norm-target-2 marked-target-2))
               (when res-2
                 (setf result res-2))))
            (t ;; nothing to do
             ))
      (values result norm-target marked-target))))

;;; try-prove-with-axioms : module List(axiom) axiom : -> { :satisfied | :ct | nil }
;;;
(defparameter .trial-context-module. (%module-decl* "trial-dummy" :object :user nil))

(defun try-prove-with-axioms (goal axioms target &optional (report-header nil))
  (let ((module (goal-context goal)))
    (with-citp-env ()
      (let ((tmodule (eval-ast .trial-context-module.)))
        (import-module tmodule :including module)
        (with-in-module (tmodule)
          (dolist (ax axioms)
            (adjoin-axiom-to-module tmodule ax)
            (set-operator-rewrite-rule tmodule ax))
          (compile-module tmodule t)
          ;; first we check contradiction
          (if (check-contradiction goal report-header)
              :ct
            ;; the module is consistent, try
            (sentence-is-satisfied target tmodule)))))))

;;; already-proved? : 
;;;
(defun already-proved? (node-or-goal &optional (warn t))
  (declare (type (or ptree-node goal) node-or-goal))
  (let ((goal (if (ptree-node-p node-or-goal)
                  (ptree-node-goal node-or-goal)
                node-or-goal)))
    (unless (goal-is-discharged goal)
      (return-from already-proved? nil))
    (when warn
      (with-output-chaos-warning ()
        (format t "** The goal ~s has already been proved!."
                (goal-name goal))))
    t))

;;; ****************************************************************************
;;; Tactic executors
;;; ****************************************************************************

;;; ===========
;;; TACTIC: NIL
;;; do nothing, but distribute multiple targets into each new goal.
;;; ===========

(defun apply-nil (node)
  (declare (ignore node))
  (with-output-chaos-warning ()
    (format t "~%Tactic [NIL] does nothing."))
  (values nil nil))

(defun apply-nil-internal (node sentences &optional (all-together nil) (tactic .tactic-nil.))
  (declare (type ptree-node node)
           (type list sentences))
  (let ((goals nil))
    (cond (all-together
           (let ((ngoal (prepare-next-goal node tactic)))
             (setf (goal-targets ngoal) sentences)
             (push ngoal goals)))
          (t (dolist (sentence sentences)
               (let ((ngoal (prepare-next-goal node tactic)))
                 (setf (goal-targets ngoal) (list sentence))
                 (push ngoal goals)))))
    (values goals (nreverse goals))))

;;; =======================
;;; TACTIC: IMPLICATION[IP]
;;; =======================

(defun generate-ip-derived-axioms (module axiom)
  (condition->axioms module (axiom-condition axiom) 'ip))

(defun simplify-eq-form (assmp)
  ;; (t1 = true) or (true = t1) ==> t1
  (when (is-builtin= (term-head assmp))
    (cond ((is-true? (term-arg-1 assmp))
           (setq assmp (term-arg-2 assmp)))
          ((is-true? (term-arg-2 assmp))
           (setq assmp (term-arg-1 assmp)))
          (t ;; do nothing
           )))
  assmp)

;;; a or b or c ... or x imply lhs
(defun make-impl-form+ (axiom assumptions)
  (flet ((make-pre (ax)
           (simplify-eq-form (make-applform *bool-sort*
                                            *eql-op*
                                            (list (axiom-lhs ax)
                                                  (axiom-rhs ax)))))
         (make-post (ax)
           (let ((op (if (eq (axiom-type ax) :equation)
                         *eql-op*
                       *rwl-predicate*)))
             (simplify-eq-form (make-applform *bool-sort*
                                              op
                                              (list (axiom-lhs ax) (axiom-rhs ax)))))))
    (if (cdr assumptions)
        (let ((as (mapcar #'make-pre assumptions)))
          (make-applform *bool-sort*
                         *bool-imply*
                         (list (make-right-assoc-normal-form *bool-and* as)
                               (make-post axiom))))
      (make-applform *bool-sort* 
                     *bool-imply*
                     (list (make-pre (car assumptions))
                           (make-post axiom))))))

(defun apply-ip (ptree-node &optional (modify-goal nil) &rest ignore)
  (declare (type ptree-node ptree-node)
           (ignore ignore))
  (with-in-context (ptree-node)
    (let ((original-goal (ptree-node-goal ptree-node)))
      (flet ((push-next-goal (goal)
               (unless (eq goal original-goal) (push goal .next-goals.))))
        (let ((target-goals (distribute-sentences ptree-node .cur-targets. .tactic-ip.)))
          (dolist (.cur-goal. target-goals)
            (let ((target (normalize-sentence (car (goal-targets .cur-goal.)) (goal-context .cur-goal.))))
              (cond ((and (not (is-true? (rule-condition target)))
                          (null (term-variables (rule-condition target))))
                     ;; t = t' if C
                     ;; C is a ground term and is not true.
                     ;; try if (SP + { C } |- t = t') or not..
                     ;; if this is satisfied, discharge it.
                     (let ((ngoal (if (eq .cur-goal. original-goal)
                                      (prepare-next-goal ptree-node .tactic-ip.)
                                    .cur-goal.)))
                       (with-in-module ((goal-context ngoal))
                         (let ((new-axs (generate-ip-derived-axioms *current-module* target))
                               (next-target (rule-copy-canonicalized target *current-module*)))
                           ;; make the target
                           (cond ((eq modify-goal :modify-goal)
                                  ;; introduce implication modifying the goal sentence
                                  ;; eq LHS = RHS --> LHS(new-axs) imply LHS = RHS .
                                  (let ((new-lhs (make-impl-form+ next-target
                                                                  new-axs))
                                        (*print-indent* (+ 2 *print-indent*)))
                                    (setf (axiom-lhs next-target) new-lhs)
                                    (setf (axiom-rhs next-target) *bool-true*)
                                    (setf (axiom-condition next-target) *bool-true*)
                                    (setf (axiom-labels next-target)
                                      (cons :ip+ (axiom-labels next-target)))
                                    (format t "~%[ip+] target sentence is converted ...")
                                    (print-next)
                                    (princ "=> ")
                                    (print-next)
                                    (print-axiom-brief next-target)
                                    (setf (goal-targets ngoal) (list next-target))))
                                 (t 
                                  ;; introduce implication as hypothesis
                                  (setf (rule-condition next-target) *bool-true*)
                                  (setf (goal-targets ngoal) (list next-target))
                                  ;; add [ip] axioms 
                                  (dolist (ax new-axs)
                                    (adjoin-axiom-to-module *current-module* ax)
                                    (set-operator-rewrite-rule *current-module* ax))
                                  (setf (goal-assumptions ngoal) 
                                    (append (goal-assumptions ngoal) (reverse new-axs)))))
                           ;; compile
                           (compile-module *current-module* t)
                           (push-next-goal ngoal)))))
                      (t 
                       ;; nothing to do
                       (push-next-goal .cur-goal.)))))
          ;; done for all goals
          (setq .next-goals. (nreverse .next-goals.))
          (dolist (ngoal .next-goals.)
            (multiple-value-bind (discharged norm-sentence org-sentence)
                (check-goal-is-satisfied ngoal 'ip)
              (declare (ignore norm-sentence org-sentence))
              (when discharged
                (format t "~%[ip] discharged the goal ~s" (goal-name ngoal)))))
          ;;
          (values .next-goals. (nreverse .next-goals.)))))))

;;; =========================
;;; TACTIC: IMPLICATION [IP+]
;;; by modifying the goal by 'imply'
;;; =========================

(defun apply-ip+ (ptree-node &rest ignore)
  (declare (type ptree-node ptree-node)
           (ignore ignore))
  (apply-ip ptree-node :modify-goal))

;;; =================================
;;; TACTIC: Theorem of Constants [TC]
;;; =================================

(defun make-tc-variable-substitutions (goal vars)
  (declare (type goal goal)
           (type list vars))
  (let ((subst nil))
    (dolist (var vars)
      (push (cons var (variable->constant goal var)) subst))
    (with-citp-debug ()
      (format t "~%[tc] variable substitution:")
      (print-next)
      (print-substitution subst))
    subst))

(defun apply-tc (ptree-node &rest ignore)
  (declare (type ptree-node ptree-node)
           (ignore ignore))
  (with-in-context (ptree-node)
    (let ((original-goal .cur-goal.))
        (flet ((push-next-goal (goal)
                 (unless (eq goal original-goal) (push goal .next-goals.))))
          (let ((target-goals (distribute-sentences ptree-node .cur-targets. .tactic-tc.)))
            (dolist (cgoal target-goals)
              ;; variables --> constants
              (let ((sentence (car (goal-targets cgoal))))
                (cond ((axiom-variables sentence)
                       (when (eq cgoal original-goal)
                         (setq cgoal (prepare-next-goal ptree-node .tactic-tc.)))
                       (push-next-goal cgoal)
                       (with-in-module ((goal-context cgoal))
                         (let* ((next-target (rule-copy-canonicalized sentence *current-module*))
                                (vars (axiom-variables next-target))
                                (subst (make-tc-variable-substitutions cgoal vars)))
                           (apply-substitution-to-axiom subst next-target 'tc t)
                           (compute-rule-method next-target)
                           (compile-module *current-module* t)
                           (setf (goal-targets cgoal)
                             (list (normalize-sentence next-target *current-module*))))))
                      (t
                       ;; the sentence does not contain any variables.
                       (push-next-goal cgoal)))))
            (setq .next-goals. (nreverse .next-goals.))
            ;; check goal is satisfied or not
            (dolist (cgoal .next-goals.)
              (multiple-value-bind (res sentence osentence)
                  (check-goal-is-satisfied cgoal 'tc)
                (declare (ignore osentence sentence))
                (when res
                  (format t "~%[tc] discharged the goal ~s" (goal-name cgoal)))))
            (values .next-goals. .next-goals.))))))

;;; ===================================
;;; TACTIC: Simultaneous Induction [SI]
;;; ===================================

;;; set-indvars : ptree-node List(variable) -> List(variable)
;;; handler of ':ind on' command
;;;
(defun set-indvars (ptree-node variables)
  (declare (type ptree-node ptree-node))
  (let* ((cur-goal (ptree-node-goal ptree-node))
         (cur-targets (goal-targets cur-goal))
         (ind-vars nil))
    (dolist (cur-target cur-targets)
      (let ((target-variables (axiom-variables cur-target)))
        (dolist (v variables)
          (let ((tv (find-if #'(lambda (x) (and (eq (variable-name v) (variable-name x))
                                                (eq (variable-sort v) (variable-sort x))))
                             target-variables)))
            (if tv (pushnew v ind-vars :test #'equal :key #'(lambda (x) (variable-name x)))
              (with-output-chaos-error ('no-such-variable)
                (format t "Setting induction variable, no such variable ~a:~a in target axiom."
                        (variable-name v) (variable-sort v))))))))
    (setf (goal-indvars cur-goal) (nreverse ind-vars))
    (format t "~%**> Induction will be conducted on ")
    (dolist (var (goal-indvars cur-goal))
      (term-print-with-sort var) (princ " "))
    ind-vars))

;;; set-induction-variables
;;; top level function.
(defun set-induction-variables (variables)
  (declare (type list variables))
  (let ((node (car (get-unproved-nodes *proof-tree*))))
    (unless node
      (with-output-chaos-error ('no-unproved)
        (format t "There is no unproved goals.")))
    (set-indvars node variables)
    (clear-induction-scheme node)))

;;;==========================================
;;; applying induction based on constructors
;;;

;;; get-induction-variable-constructors : variable -> List(constructor)
;;; returns a list of constructors of a given induction variable
;;;
(defun get-induction-variable-constructors (v constructors)
  (let ((ops nil))
    (dolist (op constructors)
      (when (sort<= (method-coarity op) (variable-sort v) (module-sort-order *current-module*))
        (push op ops)))
    (unless ops
      (with-output-chaos-error ('internal-error)
        (format t "Finding constructor of sort ~a, none was found." (string (sort-name (variable-sort v))))))
    (nreverse ops)))

;;; get-indvar-constructors
;;; returns a list of (indvar . const1 const2 ...constn) for an induction variable indvar.
;;; (((idvar-1 . const-1) ... (idvar-1 ... const-n))
;;;  ((idvar-2 . const-2) ... (idvar-2 ... const-2-m))
;;;     :
;;;  ((idva-i . const-i)  ... (idvar-i ... const-i-k)))
;;; 
(defun get-indvar-constructors (indvars constructors)
  (let ((ivar-map nil))
    (dolist (iv indvars)
      (push (mapcar #'(lambda (cts) (cons iv cts))
                    (get-induction-variable-constructors iv constructors))
            ivar-map))
    (nreverse ivar-map)))

;;; make-indvar-comb-substitutions : List(variable) List(constructor) -> List(substitution)
;;; returns all possible substitution patterns of induction variables.
;;; ex. for induction variables A, B, C, there are constructors 
;;;     op a-1 : -> A . op a-2 : ->  A
;;;     op b-1 : B -> B
;;;     op c-1 : -> C . op c-2 : -> C . op c-3 : C -> C
;;; this will produces the following substitutions:
;;; (((A . A-1) (B . B-1) (C . C-1))
;;;  ((A . A-2) (B . B-1) (C . C-2))
;;;  ((A . A-1) (B . B-1) (C . C-3))
;;;  ((A . A-2) (B . B-1) (C . C-1))
;;;  ((A . A-1) (B . B-1) (C . C-2))
;;;  ((A . A-2) (B . B-1) (C . C-3)))
;;;
(defun make-indvar-comb-substitutions (indvars constructors)
  (let ((list-of-alist (get-indvar-constructors indvars constructors)))
    (declare (type list list-of-alist))
    (select-comb-elems list-of-alist)))

;;; get-induction-base-substitutions : List(substitution) -> List(substitution)
;;;
(defun get-induction-base-substitutions (all-subst)
  (let ((res nil))
    (dolist (subst all-subst)
      (when (every #'(lambda (sub) (null (method-arity (cdr sub)))) subst)
        (push subst res)))
    (with-citp-debug ()
      (format t "~%[si] base case subst")
      (dolist (sub res)
        (print-next)
        (print-substitution sub)))
    (nreverse res)))

;;; get-induction-step-substitutions : List(substitution) -> List(substitution)
;;;
(defun get-induction-step-substitutions (all-subst)
  (let ((res nil))
    (dolist (subst all-subst)
      (unless (every #'(lambda (sub) (null (method-arity (cdr sub)))) subst)
        (push subst res)))
    (with-citp-debug ()
      (format t "~%[si] get-induction-step-subsutitutions")
      (dolist (sub res)
        (print-next)
        (print-substitution sub)))
    (nreverse res)))

;;; get-real-target-variable : variable List(variable) -> { variable | null }
;;; finds an variable from a list of variables.
;;;
(defun get-real-target-variable (indvar axiom-variables)
  (find-if #'(lambda (m) (and (sort= (variable-sort m) (variable-sort indvar))
                              (equal (variable-name m) (variable-name indvar))))
           axiom-variables))

;;; make-real-induction-subst
;;;
(defun make-real-induction-subst (subst axiom-vars)
  (let ((rsubst nil))
    (dolist (sub subst)
      (let* ((iv (car sub))
             (op-or-term (cdr sub))
             (term (if (term? op-or-term)
                       (term-copy-and-returns-list-variables op-or-term)
                     (make-applform (method-coarity op-or-term)
                                    op-or-term
                                    nil)))
            (rv nil))
        (when (setq rv (get-real-target-variable iv axiom-vars))
          (setq rsubst (acons rv term rsubst)))))
    rsubst))

;;; set-base-cases
;;; generates base case axioms for a given target 
;;;
(defun set-base-cases (goal target base-substitutions)
  (let ((all-targets nil)
        (app? nil))
    (with-in-module ((goal-context goal))
      (dolist (subst base-substitutions)
        (let* ((new-target (rule-copy-canonicalized target *current-module*))
               (real-subst (make-real-induction-subst subst (axiom-variables new-target))))
          (when real-subst
            (setq app? t)
            (apply-substitution-to-axiom real-subst new-target 'induction-base)
            (push new-target all-targets)))))
    (setf (goal-targets goal) (nconc (goal-targets goal) all-targets))
    app?))

;;; make-step-constructor-term
;;;
(defun make-step-constructor-term (goal op one-arg variable)
  (with-in-module ((goal-context goal))
    (let ((arity (method-arity op))
          (arg-list nil)
          (arg-var-assoc nil)
          (n 0))
      (setq arg-var-assoc
        (mapcar #'(lambda (x) (cons x 0)) arity))
      (dolist (s arity)
        (cond ((sort<= (term-sort one-arg) s *current-sort-order*)
               (when (< 1 (incf n))
                 (with-output-chaos-error ('sorry)
                   (format t "Sorry, but system does not handle a constructor having multiple arguments of the same sort.")))
               (push one-arg arg-list))
              (t (let* ((var-assoc (assoc s arg-var-assoc))
                        (ind-var (if (zerop (cdr var-assoc))
                                     (progn (incf (cdr var-assoc)) variable)
                                   (make-variable-term s 
                                                       (intern (format nil "~A~D" 
                                                                       (string (variable-name variable))
                                                                       (incf (cdr var-assoc)))))))
                        (constant (variable->constructor goal ind-var :sort s)))
                   (push constant arg-list)))))
      (let ((res (make-applform (method-coarity op) op (nreverse arg-list))))
        res))))

;;; make-induction-step-subst : goal axiom (var . op-or-term) -> substitution
;;; 
(defun make-induction-step-subst (goal target v-op-list)
  ;; we ignore all mapped operators are constant constructors.
  (when (every #'(lambda (v-op)
                   (let ((op (cdr v-op)))
                     (and (null (method-arity op))
                          (method-is-constructor? op))))
                v-op-list)
    (return-from make-induction-step-subst nil))
  (make-induction-step-subst-from-op goal target v-op-list))

(defun make-induction-step-subst-from-op (goal target v-op-list)
  (let ((hypo-v-op nil) 
        (step-v-op nil)
        (axiom-vars (axiom-variables target)))
    ;; we generate the following case for each induction variable v:
    ;; 1) (v . <term of constant constructor>)
    ;; 2) (v . <constant term of non-constant-constructor>)
    ;; 3) (v . <application form of non-constant-constructor>)
    ;;
    (dolist (sub v-op-list)
      (let* ((iv (car sub))   ; induction variable
             (op (cdr sub))   ; operator
             (rv nil))        ; real induction variable in target
        (when (setq rv (get-real-target-variable iv axiom-vars))
          (cond ((null (method-arity op))
                 (let* ((ct (variable->constructor goal rv :op op))
                        (c-subst (cons iv ct)))
                   ;; operator is constant constructor
                   (push (list (cons iv (list op ct))) hypo-v-op)
                   (push c-subst step-v-op)))
                (t ;; operator is non-constant constructor
                 (let ((const-term (variable->constructor goal rv)))
                   (push (list (cons rv (list op const-term))) hypo-v-op)
                   (push (cons rv (make-step-constructor-term goal op const-term rv)) step-v-op)))))))
    (values (select-comb-elems (nreverse hypo-v-op))
            (nreverse step-v-op))))

(defun make-real-induction-step-subst (subst variables)
  (let ((rsubst nil))
    (dolist (sub subst)
      (let ((iv (car sub))
            (term (cdr sub))
            (rv nil))
        (when (setq rv (get-real-target-variable iv variables))
          (setq rsubst (acons rv term rsubst)))))
    (nreverse rsubst)))

(defun resolve-induction-subst (goal hypo-v-op step-subst)
  (declare (ignore goal))
  (flet ((make-proper-alist (sub)
           (mapcar #'(lambda (s) (cons (car s) (cadr s))) sub)))
    (unless hypo-v-op 
      (with-output-chaos-warning ()
        (format t "No subst given.")
        (return-from resolve-induction-subst nil)))
    (let ((rsubsts (mapcar #'(lambda (sub)
                               (cons (car sub) (list (third sub))))
                           hypo-v-op))
          (all-subst nil))
      (with-citp-debug ()
        (format t "~%[si] resolve induction step: given")
        (print-next) (format t "hypo-v-op: ~s" hypo-v-op)
        (print-next) (princ "step-subst" )
        (print-substitution step-subst))
      ;; return if there are no possible combinations
      ;; (unless (cdr hypo-v-op)
      ;;   (return-from resolve-induction-subst (list (make-proper-alist rsubsts))))
      ;;
      (with-citp-debug ()
        (format t "~%resolve subst: given")
        (dolist (v-op hypo-v-op)
          (let ((*print-indent* (+ 2 *print-indent*)))
            (print-next)
            (format t "(~a . ~a <- " (variable-name (first v-op)) (car (method-name (second v-op))))
            (term-print-with-sort (third v-op))
            (princ ")"))))

      ;; make all possible hypothesis substitutions
      (let ((vop-hash (make-hash-table :test #'eq))
            (vcombs nil))
        (dolist (v-op hypo-v-op)
          (let ((v (first v-op))
                (as nil))
            (unless (setq as (assoc v rsubsts))
              (with-output-chaos-error ('internal-err)
                (format t "!! cannot find variable subst ~s" (variable-name v))))
            (setf (gethash v vop-hash) (list as))
            (let ((st (assoc v step-subst :test #'equal))
                  (hentry (gethash v vop-hash))
                  (new-element nil))
              (unless st (with-output-chaos-error ('no-step-term)
                           (format t "No step term found for variable ~a" (variable-name v))))
              (setq new-element (cons v (list (cdr st))))
              (unless (member new-element hentry :test #'equal)
                (setf (gethash v vop-hash) (append hentry (list new-element)))))))
        (maphash #'(lambda (x vl) (declare (ignore x)) (push vl vcombs)) vop-hash)
        (setq all-subst (select-comb-elems vcombs))
        (with-citp-debug ()
          (format t "~%resolve subt: all possibilities")
          (let ((*print-indent* (+ 2 *print-indent*))
                (num 0))
            (declare (type fixnum num))
            (dolist (vcom all-subst)
              (print-next)
              (format t "=== (#~d) " (incf num))
              (dolist (rs vcom)
                (format t "~a |-> " (variable-name (car rs)))
                (term-print-with-sort (cadr rs)) (princ " ")))))
        ;;
        (mapcar #'make-proper-alist all-subst)))))

;;; add-hypothesis
;;; Note: assumes computing module context is established.
;;;
(defun subst-is-equal (sub1 sub2)
  (dolist (entry sub1)
    (let ((entry2 (assoc (car entry) sub2 :test #'equal)))
      (unless entry2 (return-from subst-is-equal nil))
      (unless (equal (cdr entry) (cdr entry2))
        (return-from subst-is-equal nil))))
  t)

(defun add-hypothesis (step-goal target hypo-subst step-subst)
  (with-citp-debug ()
    (format t "~%[si] add-hypothesis:")
    (print-next) (princ "-- hypo-subst ")
    (dolist (hp hypo-subst)
      (print-next)
      (print-substitution hp))
    (print-next) (princ "-- step-subst ")
    (print-substitution step-subst))
  (dolist (osub hypo-subst)
    (dolist (sub (resolve-induction-subst step-goal osub step-subst))
      (unless (subst-is-equal sub step-subst)
        (let* ((hypo (rule-copy-canonicalized target *current-module* nil :delete-non-exec))
               (subst (make-real-induction-step-subst sub (axiom-variables hypo))))
          (with-citp-debug
              (format t "~%[applying hypo subst] ")
            (print-substitution subst)
            (print-next)
            (princ "to ")
            (print-axiom-brief hypo))
          (apply-substitution-to-axiom subst hypo 'si t) 
          (compute-rule-method hypo)
          (set-operator-rewrite-rule *current-module* hypo)
          (adjoin-axiom-to-module *current-module* hypo)
          (with-citp-debug ()
            (format t "~%--> ")
            (print-axiom-brief hypo))
          (setf (goal-assumptions step-goal) (append (goal-assumptions step-goal) (list hypo))))))))

;;; add-step-cases
;;; Note: assumes computing module context is established.
;;;
(defun add-step-cases (step-goal target step-subst)
  (let* ((new-target (rule-copy-canonicalized target *current-module*))
         (subst (make-real-induction-step-subst step-subst (axiom-variables new-target))))
    (when (car subst)
      (with-citp-debug
        (format t "~%[applying step subst] ")
        (print-substitution subst))
      (apply-substitution-to-axiom subst new-target 'step)
      (setf (goal-targets step-goal) (nconc (goal-targets step-goal) (list new-target))))))
                                
;;; induction-cases
;;; Note: assumes there properly set induction variables in the current goal.
;;;
(defun get-induction-constructors (current-goal)
  (declare (ignore current-goal))
  (ptree-constructor-ops *proof-tree*))

(defun induction-cases (parent-node)
  (declare (type ptree-node parent-node))
  (let* ((cur-goal (ptree-node-goal parent-node))
         (cur-targets nil)
         (indvars (goal-indvars cur-goal))
         (all-subst (make-indvar-comb-substitutions indvars
                                                    (get-induction-constructors cur-goal)))
         (base-goal (prepare-next-goal parent-node .tactic-si.))
         (step-goals nil)
         (need-goal nil)
         (base-generated nil)
         (remainings nil))
    ;;
    (with-citp-debug ()
      (format t "~%[si] all possible substitutions")
      (let ((num 0))
        (declare (type fixnum num))
        (dolist (subs all-subst)
          (format t "~%subst #~d" (incf num))
          (let ((*print-indent* (+ 2 *print-indent*)))
            (print-next)
            (print-substitution subs)))))

    ;; implicit NF application
    (dolist (ct (goal-targets cur-goal))
      (multiple-value-bind (ntarget app?)
          (normalize-sentence ct (goal-context cur-goal))
        (when app? (setq need-goal t))
        (push ntarget cur-targets)))
    (setq cur-targets (nreverse cur-targets))

    ;; generate base cases
    ;;
    (dolist (target cur-targets)
      (if (not (set-base-cases base-goal target (get-induction-base-substitutions all-subst)))
          (when need-goal
            (push target remainings))
        (setq base-generated t)))
    (unless base-generated (setq base-goal nil))
    
    ;; generate step cases
    ;; we generate all possible combinations of given induction variables.
    ;; for each combination, we will construct a new goal.
    ;;
    (dolist (subst (get-induction-step-substitutions all-subst))
      (let ((step-goal (prepare-next-goal parent-node .tactic-si.)))
        (with-in-module ((goal-context step-goal))
          ;; following functions and their callies can assume the computing context is established.
          (dolist (target cur-targets)
            (multiple-value-bind (hypo-subst-list step-subst)
                (make-induction-step-subst step-goal target subst)
              (add-hypothesis step-goal target hypo-subst-list step-subst)
              (add-step-cases step-goal target step-subst)))
          (cond ((goal-targets step-goal)
                 (push step-goal step-goals))
                (t )))))                ; do nothig
    ;;
    (when remainings
      (multiple-value-bind (ap? nil-goals)
          (apply-nil-internal parent-node (reverse remainings) :all-togather .tactic-si.)
        (declare (ignore ap?))
        (dolist (ng nil-goals)
          (push ng step-goals))))
    ;; 
    (if base-goal
        (values t (cons base-goal (nreverse step-goals)))
      (if step-goals
          ;; case remainings 
          (values t step-goals)
        (values nil nil)))))

;;; apply-si : ptree-node tactic -> (applied? . List(goal))
;;;
(defun apply-si (ptree-node &rest ignore)
  (declare (type ptree-node ptree-node)
           (ignore ignore))
  (let ((cur-goal (ptree-node-goal ptree-node)))
    (unless (and (goal-indvars cur-goal) (goal-targets cur-goal))
      (return-from apply-si nil))
    (multiple-value-bind (applied new-goals)
        (induction-cases ptree-node)
      (if applied
          (values applied new-goals)
        (values nil nil)))))

;;; =======================================
;;; applying user defined induction scheme
;;;
(defun set-induction-variables-and-scheme (node variables bases hypos steps)
  (declare (type list variables bases steps))
  (let ((goal-node (ptree-node-goal node)))
    (set-indvars node variables)
    (set-indbases goal-node bases)
    (set-indhypos goal-node hypos)
    (set-indsteps goal-node steps)))

(defun set-indbases (goal-node terms)
  (setf (goal-bases goal-node) terms)
    (let ((bases (goal-bases goal-node)))
      (format t "~%--> :ind{} setting induction base~p" (length bases))
      (dolist (b bases)
        (let ((*print-indent* (+ 2 *print-indent*)))
          (print-next)
          (term-print b)))
      (flush-all)))

(defun set-indhypos (goal-node terms)
  (setf (goal-hypos goal-node) terms)
  (let ((hypos (goal-hypos goal-node)))
    (format t "~%--> :ind{} setting hypothesis pattern~p" (length hypos))
    (dolist (h hypos)
      (let ((*print-indent* (+ 2 *print-indent*)))
        (print-next)
        (term-print h)))
    (flush-all)))

(defun set-indsteps (goal-node terms)
    (setf (goal-steps goal-node) terms)
    (let ((steps (goal-steps goal-node)))
      (format t "~%--> :ind{} setting induction step~p" (length steps))
      (dolist (s steps)
        (let ((*print-indent* (+ 2 *print-indent*)))
          (print-next)
          (term-print s)))
      (flush-all)))

(defun get-ind-substitutions (indvars bases)
  (let ((ivar-map nil))
    (dolist (var indvars)
      (let ((vsort (variable-sort var)))
        (let ((subst nil))
          (dolist (base bases)
            (when (sort= vsort (term-sort base))
              (push (cons var base) subst)))
          (when subst
            (push subst ivar-map)))))
    (with-citp-debug ()
      (when ivar-map
        (format t "~%--> :ind{}: substitution")
        (let ((*print-indent* (+ 2 *print-indent*)))
          (dolist (subst ivar-map)
            (print-next)
            (print-substitution subst)))))
    (nreverse ivar-map)))

(defun make-induction-step-subst-from-term (goal target v-term-list)
  (let ((hypo-v-op nil) 
        (step-v-op nil)
        (axiom-vars (axiom-variables target)))
    ;; we generate the following case for each induction variable v:
    ;; 1) (v . <term of constant constructor>)
    ;; 2) (v . <constant term of non-constant-constructor>)
    ;; 3) (v . <application form of non-constant-constructor>)
    ;;
    (dolist (sub v-term-list)
      (let* ((iv (car sub))   ; induction variable
             (term (cdr sub)) ; term
             (op (term-head term))
             (rv nil))        ; real induction variable in target
        (when (setq rv (get-real-target-variable iv axiom-vars))
          (cond ((null (term-subterms term))
                 (let* ((ct (variable->constructor goal rv :op op))
                        (c-subst (cons iv ct)))
                   ;; operator is constant constructor
                   (push (list (cons iv (list op ct))) hypo-v-op)
                   (push c-subst step-v-op)))
                (t ;; operator is non-constant constructor
                 (let ((const-term (variable->constructor goal rv)))
                   (push (list (cons rv (list op const-term))) hypo-v-op)
                   (push (cons rv (make-step-constructor-term goal op const-term rv)) step-v-op)))))))
    (values (select-comb-elems (nreverse hypo-v-op))
            (nreverse step-v-op))))

;;; user-induction-cases
;;;
(defun user-induction-cases (ptree-node)
  (declare (type ptree-node ptree-node))
  (let ((goal (ptree-node-goal ptree-node)))
    (let* ((*chaos-quiet* t)
           (indvars (goal-indvars goal))
           (targets (goal-targets goal))
           (base-generated nil)
           (base-goal (prepare-next-goal ptree-node .tactic-ind.))
           (given-hypos (goal-hypos goal))
           (step-goals nil)
           (remainings nil))
      ;; just for now
      (declare (ignore given-hypos))
      ;; base cases
      (dolist (target targets)
        (if (not (set-base-cases base-goal target (get-ind-substitutions indvars (goal-bases goal))))
            (push target remainings)
          (setq base-generated t)))
      (unless base-generated (setq base-goal nil))
      ;; step cases 
      (dolist (subst (get-ind-substitutions indvars (goal-steps goal)))
        (let ((step-goal (prepare-next-goal ptree-node .tactic-ind.)))
          (with-in-module ((goal-context step-goal))
            (dolist (target targets)
              (multiple-value-bind (hypo-subst-list step-subst)
                  (make-induction-step-subst-from-term step-goal target subst)
                (add-hypothesis step-goal target hypo-subst-list step-subst)
                (add-step-cases step-goal target step-subst)))
            (cond ((goal-targets step-goal)
                   (push step-goal step-goals))
                  (t )))))              ; do nothing
      ;; 
      (when remainings
        (multiple-value-bind (ap? nil-goals)
            (apply-nil-internal ptree-node (reverse remainings) :all-togather .tactic-ind.)
          (declare (ignore ap?))
          (dolist (ng nil-goals)
            (push ng step-goals))))
      ;;
      (if base-goal
          (values t (cons base-goal (nreverse step-goals)))
        (values nil nil)))))

;;; apply-user-defined-induction-scheme
;;;
(defun apply-user-defined-induction-scheme (ptree-node)
  (declare (type ptree-node ptree-node))
  (multiple-value-bind (applied new-goals)
      (user-induction-cases ptree-node)
    (when applied
      ;; add generated nodes as children
      (add-ptree-children ptree-node new-goals)
      (when-citp-verbose ()
        (dolist (gn (ptree-node-subnodes ptree-node))
          (pr-goal (ptree-node-goal gn))))
      (ptree-node-subnodes ptree-node))))

;;; =======================
;;; TACTIC: REDUCTION [RD]
;;; =======================

;;; do-apply-rd
;;; 
(defun do-apply-rd (cur-goal next-goal do-undo tactic)
  (let* ((target-goal (or next-goal cur-goal))
         (cur-targets (goal-targets target-goal))
         (reduced-targets nil)
         (discharged nil)
         (result nil)
         (tactic-name (tactic-name tactic)))
    (unless cur-targets 
      (with-citp-debug ()
        (format t "~%[rd] no target sentences."))
      (return-from do-apply-rd (values nil nil)))
    (compile-module (goal-context target-goal) t)
    (dolist (target cur-targets)
      (multiple-value-bind (c-result cur-target original-sentence)
          (do-check-sentence target (or next-goal cur-goal) tactic-name)
        (cond (c-result                 ; satisfied or contradition
               (setq result t)
               (push original-sentence discharged))
              ;; reduced but not discharged
              (t (if do-undo
                     (push original-sentence reduced-targets)
                   (push cur-target reduced-targets))))))
    ;; set new (reduced sentences) as targets
    (setf (goal-targets target-goal) (nreverse reduced-targets))
    ;; set discharged sentences 
    (setf (goal-proved cur-goal) (nreverse discharged))
    (unless reduced-targets
      ;; this means all sentences are discharged
      (setf (goal-targets cur-goal) nil)
      (format t "~%[~a] discharged goal ~s." tactic-name (goal-name cur-goal))
      (return-from do-apply-rd (values result nil)))
    ;; there remains 
    (values t (list (or next-goal cur-goal)))))

;;; apply-rd-internal : ptree-node undo? tactic
;;; working horse of apply-rd(-)
;;;
(defun apply-rd-internal (ptree-node do-undo &optional (tactic .tactic-rd.))
  (declare (type ptree-node ptree-node)
           (type tactic tactic))
  ;; we set :spoiler on
  ;; forcing application of implicit tactics(NF,CF, e.t.c.)
  (with-spoiler-on ()
    (let ((cur-goal (ptree-node-goal ptree-node)))
      (when (goal-is-discharged cur-goal)
        (with-output-chaos-warning ()
          (format t "** The goal ~s has already been proved!"
                  (goal-name cur-goal)))
        (return-from apply-rd-internal (values nil nil)))
      (unless (goal-targets cur-goal)
        (return-from apply-rd-internal nil))
      (let ((undo? (or do-undo (the-goal-needs-undo cur-goal))))
        ;; undo? = true means the current goal is generatd by 
        ;; :defined :ctf- or :csp-, AND
        ;; this RD application follows it, i.e., :apply(... ctf-n rd ...)
        ;; in this case we don't prepare next-goal and ..
        (let ((next-goal (if undo?
                             nil
                           (prepare-next-goal ptree-node .tactic-rd.))))
          (unless undo?
            (setf (goal-targets next-goal) (goal-targets cur-goal)))
          (with-citp-debug ()
            (format t "~%[rd] target: ~a" (if next-goal
                                              (goal-name next-goal)
                                            (goal-name cur-goal))))
          (multiple-value-bind (applied next-goals)
              (do-apply-rd cur-goal next-goal undo? tactic)
            (declare (ignore applied))
            (if undo?
                ;; the original goal rolled back, no new goal is needed.
                (values next-goals nil)
              (values next-goals next-goals))))))))

;;; apply-rd
;;; explicit application of tactic RD.
(defun apply-rd (ptree-node &optional (tactic .tactic-rd.))
  (apply-rd-internal ptree-node nil tactic))

;;; apply-rd-
;;; explicit application of tactic RD,
;;; but if the sentence was not reduced to 'true'
;;; preserves the original goal sentence
;;;
(defun apply-rd- (ptree-node &optional (tactic .tactic-rd-.))
  (apply-rd-internal ptree-node :undo tactic))

;;; ==========================
;;; TACTIC: Case Analysis [CA]
;;; ==========================

;;; get-gterms : term -> List(ground-term)
;;; returns a list of ground terms in given term.
;;;
(defun get-gterms (term)
  (declare (type term term))
  (let ((gterms nil))
    (declare (type list gterms))
    (when (term-is-applform? term)
      (unless (term-variables term)
        (push term gterms))
      (dolist (arg (term-subterms term))
        (setq gterms (nconc gterms (get-gterms arg)))))
    gterms))

;;; get-gterms-from-axiom : axiom -> List(ground-term)
;;; returns the list of ground terms contained in the given axiom.
;;;
(defun get-gterms-from-axiom (axiom &optional (condition-only nil))
  (declare (type axiom axiom))
  (let ((gterms nil))
    (declare (type list gterms))
    (cond (condition-only
           (unless (is-true? (axiom-condition axiom))
             (setq gterms (remove-duplicates (get-gterms (axiom-condition axiom))
                                             :test #'equal))))
          (t (setq gterms (delete-duplicates (append (get-gterms (axiom-lhs axiom))
                                                     (append (get-gterms (axiom-rhs axiom))
                                                             (get-gterms-from-axiom axiom t)))
                                   :test #'equal))))

    gterms))

;;; gsubterm-has-matching-rule : term List(axiom) -> Bool
;;; returns t iff there is an axiom x in List(axiom) st.
;;; sigma(s) = lhs(x), where s is one of the true subterm of given ground term.
;;;
(defun gsubterm-has-matching-rule (gterm c-rules)
  (declare (type term gterm)
           (type list c-rules))
  (dolist (term (delete gterm (get-gterms gterm)))
    (with-citp-debug ()
      (format t "~%  check : ")
      (term-print-with-sort term))
    (dolist (crule c-rules)
      (multiple-value-bind (gs sub no-match eeq)
          (@matcher (axiom-lhs crule) term :match)
        (declare (ignore eeq sub gs))
        (unless no-match
          (return-from gsubterm-has-matching-rule t)))))
  nil)

;;; ca-instantiate-condition : goal term -> term'
;;; returns a term t' by replacing every variable in the given term t
;;; by a constant.
;;;
(defun ca-instantiate-condition (goal condition)
  (declare (type goal goal)
           (type term condition))
  (let ((vars (term-variables condition))
        (subst nil))
    (declare (type list vars subst))
    (cond (vars (dolist (v vars)
                  (push (cons v (variable->constant goal v)) subst))
                (substitution-image-simplifying subst condition))
          (t condition))))

;;; find-gterm-matching-conditionals : goal term List(conditional axioms) 
;;;                                    -> List(<subst, axiom, condition>)
;;; returns all possible cases for a given ground term.
;;;
(defvar .duplicated. nil)
(defvar .subst-so-far. nil)


(defun find-gterm-matching-conditionals (goal gterm conditional-rules idx)
  (declare (type goal goal)
           (type term gterm)
           (type list conditional-rules)
           (type fixnum idx))
  (let ((res nil)
        (rejected nil))
    (dolist (rule conditional-rules)
      (block next
        (unless (is-true? (rule-condition rule))
          (multiple-value-bind (gs sub no-match eeq)
              (@matcher (axiom-lhs rule) gterm :match)
            (declare (ignore eeq))
            (when no-match (return-from next nil))
            (let ((cond-instance
                   (ca-instantiate-condition goal
                                             (substitution-image-simplifying sub (rule-condition rule)))))
              (cond ((not (member cond-instance .subst-so-far. :test #'term-equational-equal))
                     (push cond-instance .subst-so-far.)
                     (push cond-instance res))
                    (t 
                     (push cond-instance rejected)))
              (loop 
                (let ((n-subst nil)
                      (n-cond-inst nil))
                  (multiple-value-setq (gs n-subst no-match)
                    (next-match gs))
                  (when no-match (return-from next))
                  (with-citp-debug ()
                    (format t "~%[ca] adding extra."))
                  (setq n-cond-inst
                    (ca-instantiate-condition goal
                                              (substitution-image-simplifying n-subst (rule-condition rule))))
                  (cond ((not (member n-cond-inst .subst-so-far. :test #'term-equational-equal))
                         (unless (term-equational-equal n-cond-inst cond-instance)
                           (push n-cond-inst .subst-so-far.)
                           (push n-cond-inst res)))
                        (t 
                         ;; (push cond-instance res) ; ***
                         (push cond-instance rejected))))))))))
    ;;
    (with-citp-debug ()
      (when res
        (format t "~%found cases for ") (term-print-with-sort gterm)
        (dolist (i res)
          (print-next)
          (term-print-with-sort i)))
      (when rejected
        (format t "~%rejected cases")
        (dolist (i rejected)
          (print-next)
          (term-print-with-sort i))))
    (when rejected
      (setf (aref .duplicated. idx) (remove-duplicates rejected :test #'term-equational-equal)))
    ;;
    (remove-duplicates res :test #'term-equational-equal)))

;;; generate-case-axioms : goal List(< rule . subst >) -> List(axiom)
;;;
(defvar .new-axs-so-far. nil)

(defun generate-case-axioms (next-goal conditions)
  (with-in-module ((goal-context next-goal))
    (let ((case-axioms nil))
      (dolist (condition conditions)
        (let ((list-lhs nil))
          (if (method= *bool-cond-op* (term-head condition))
              (dolist (arg (list-assoc-subterms condition *bool-cond-op*))
                (push arg list-lhs))
            (setq list-lhs (list condition)))
          (dolist (condition list-lhs)
            (let ((axs (make-new-assumption *current-module* condition 'ca)))
              (when axs
                (unless (member axs .new-axs-so-far. :test #'rule-is-similar?)
                  (push axs .new-axs-so-far.)
                  (compute-rule-method axs)
                  (with-citp-debug ()
                    (format t "~%[ca] adding an axiom to module ~s" (get-module-simple-name (goal-context next-goal)))
                    (print-next)
                    (print-axiom-brief axs))
                  (set-operator-rewrite-rule *current-module* axs)
                  (adjoin-axiom-to-module *current-module* axs)
                  (push axs case-axioms)))))))
      (compile-module *current-module* t)
      (setf (goal-assumptions next-goal) (append (goal-assumptions next-goal)
                                                 (nreverse case-axioms))))))
                                                   
;;; normalize-cases : List(List(term)) -> List(List(term))'
;;;

(defun find-sub-case-in (case l-case)
  (declare (type list case l-case))
  (let ((size (length case)))
    (declare (type fixnum size))
  (dolist (xc l-case)
    (when (and (<= size (length xc))
               (every #'(lambda (x) (find x xc :test #'term-equational-equal)) case))
      (return-from find-sub-case-in xc)))
  nil))

(defun case-is-valid (idxs term)
  (dolist (idx idxs)
    (when (member term (aref .duplicated. idx) :test #'term-equational-equal)
      (with-citp-debug ()
        (format t "~% ... rejected."))
      (return-from case-is-valid nil)))
  term)

(defun remove-exclusive-cases (case)
  (let ((idxs (mapcar #'(lambda (x) (car x)) case))
        (result nil))
    (declare (type list idxs result))
    (with-citp-debug ()
      (format t "~%-- check these combination")
      (dolist (c case)
        (print-next)
        (format t "~idx ~d: " (car c))
        (term-print-with-sort (cdr c))))
    (dolist (c case)
      (let ((term (cdr c)))
        (when (case-is-valid idxs term)
          (push term result))))
    result))

(defun normalize-cases (l-case ptree-node all-cases)
  (declare (type list l-case)
           (type ptree-node ptree-node))
  (let ((mod (goal-context (ptree-node-goal ptree-node)))
        (dist-cases nil))
    (with-in-module (mod)
      (flet ((distribute-cond (term)
               (if (method= *bool-cond-op* (term-head term))
                   (list-assoc-subterms term *bool-cond-op*)
                 (list term))))
        (with-citp-debug ()
          (when .duplicated.
            (format t "~%== .duplicated. === ")
            (dotimes (x (1- (length .duplicated.)))
              (format t "~%(~d)" x)
              (dolist (trm (aref .duplicated. x))
                (print-next)
                (term-print-with-sort trm)))))
        (dolist (case l-case)
          (block next
            ;; case ::= (t0 t1 ... tn)
            ;; first we remove exclusive cases
            (setq case (remove-exclusive-cases case))
            (unless case (return-from next nil))
            (dolist (c case)
              (setq all-cases (delete c all-cases :test #'term-equational-equal)))
            ;; then divide /\ into each cases
            (let ((dcase nil))
              (dolist (c case)
                (setq dcase (nconc dcase (distribute-cond c))))
              (push (delete-duplicates dcase :test #'term-equational-equal) dist-cases)))
          (setq dist-cases (nreverse dist-cases)))
        ;; 
        (let ((result nil))
          ;; for each case
          (dolist (case dist-cases)
            (unless (find-sub-case-in case result)
              (setq result (nconc result (list case)))))
          (when all-cases
            ;; remaining sole cases
            (dolist (c all-cases)
              (push (list c) result)))
          ;;
          result)))))

;;; generate-cases : ptree-node term List(conditional-axiom)
;;;
(defun generate-cases (ptree-node target conditional-rules divide?)
  (declare (type ptree-node ptree-node)
           (list conditional-rules))
  (multiple-value-bind (norm-target app?)
      (normalize-sentence target (goal-context (ptree-node-goal ptree-node)))
    (when app?
      (setq target norm-target))
    (with-citp-debug ()
      (format t "~%** Case Analysis: target -----------")
      (print-next)
      (print-axiom-brief target))
    ;; then generate possible cases
    (let ((gterms (get-gterms-from-axiom target))
          (next-goals nil)
          (remainings nil)
          (all-cases nil)
          (gt-idx 0)
          (.subst-so-far. nil)
          (.duplicated. nil))
      (declare (type fixnum gt-idx)
               (type list gterms next-goals remainings .subst-so-far.))
      (setf .duplicated. (make-array (length gterms) :initial-element nil))
      ;; 
      (let ((g-conditions nil))
        (dolist (gterm gterms)
          (unless (gsubterm-has-matching-rule gterm conditional-rules)
            (let ((conds (find-gterm-matching-conditionals (ptree-node-goal ptree-node)
                                                           gterm
                                                           conditional-rules
                                                           gt-idx)))
              (when conds
                (incf gt-idx)
                (push conds g-conditions)))))
        (setq g-conditions (nreverse g-conditions))
        (with-citp-debug ()
          (format t "~%All the conditions")
          (print-next)
          (dolist (gc g-conditions)
            (princ "====") 
            (print-next)
            (dolist (cond  gc)
              (term-print-with-sort cond))))
        ;;
        (dolist (gc g-conditions)
          (dolist (c gc)
            (pushnew c all-cases :test #'term-equational-equal)))

        ;; make all combinations and generate cases
        (let ((rv-combs (select-comb-elems g-conditions t))
              (next-goal nil))
          ;; distribute /\  and delete duplicated conditions
          (with-citp-debug ()
            (format t "~%[ca] gterm conditions --BEFORE normalization: ")
            (if rv-combs
                (let ((rv-com nil))
                  (dotimes (x (length rv-combs))
                    (setq rv-com (nth x rv-combs))
                    (print-next)
                    (format t "--(~d)--" (1+ x))
                    (dolist (rr rv-com)
                      (print-next)
                      (format t "~d:" (car rr))
                      (term-print-with-sort (cdr rr)))))
              (format t "NONE.")))
          ;; eliminate exclusive combinations and dupulicated cases.
          (setq rv-combs (normalize-cases rv-combs ptree-node all-cases))
          
          (with-citp-debug ()
            (format t "~%[ca] gterm conditions --AFTER normalization: ")
            (if rv-combs
                (let ((rv-com nil))
                  (dotimes (x (length rv-combs))
                    (setq rv-com (nth x rv-combs))
                    (print-next)
                    (format t "--(~d)--" (1+ x))
                    (dolist (rr rv-com)
                      (print-next)
                      (term-print-with-sort rr))))
              (format t "NONE.")))
          (cond (rv-combs
                 (dolist (rv-com rv-combs)
                   (let ((.new-axs-so-far. nil))
                     (setq next-goal (prepare-next-goal ptree-node .tactic-ca.))
                     (setf (goal-targets next-goal) (list target))
                     (generate-case-axioms next-goal rv-com)
                     (push next-goal next-goals)))
                 ;; normalize the target after adding cases
                 (normalize-sentence target *current-module*))
                (t
                 ;; no case is generated for the target
                 (push target remainings)))))
      ;;
      (when remainings
        (when (or next-goals app? divide?)
          (multiple-value-bind (app? nop-goals)
              (apply-nil-internal ptree-node (reverse remainings) nil .tactic-ca.)
            (declare (ignore app?))
            (if-spoiler-on
             :then (dolist(ng nop-goals)
                     (let ((target (car (goal-targets ng))))
                       ;; no case is generated: apply normalization & check the result
                       (multiple-value-bind (discharged normalized-target original-target)
                           (do-check-sentence target ng)
                         (when discharged
                           (format t "~%[ca] discharged: ")
                           (print-axiom-brief normalized-target)
                           (setf (goal-targets ng) nil
                                 (goal-proved ng) (list original-target))))
                       (push ng next-goals)))
             :else (setq next-goals nop-goals)))))
      ;; check LE
      (setq next-goals (nreverse next-goals))
      (dolist (goal next-goals)
        (check-le goal))
      ;;
      (values next-goals next-goals))))

(defun rule-is-for-case (rule)
  (and (not (is-true? (rule-condition rule)))
       (let ((labels (rule-labels rule)))
         (dolist (lb labels nil)
           (let ((lstr (string lb)))
             (when (and (>= (length lstr) 3)
                        (string-equal (subseq lstr 0 3) "CA-"))
               (return-from rule-is-for-case t)))))))

(defun get-ca-rules (module)
  (remove-if-not #'rule-is-for-case (module-all-rules module)))

;;; apply-ca
;;; toplevel of :ca
(defun apply-ca (ptree-node &rest ignore)
  (declare (type ptree-node ptree-node)
           (ignore ignore))
  (with-in-context (ptree-node)
    (with-in-module ((goal-context .cur-goal.))
      (let ((crules (get-ca-rules *current-module*))
            (divide? (cdr .cur-targets.)))
        (dolist (target .cur-targets.)
          (multiple-value-bind (applied goals)
              (generate-cases ptree-node target crules divide?)
            (declare (ignore applied))
            (when goals (setq .next-goals. (nconc .next-goals. goals)))))
        (values .next-goals. .next-goals.)))))

;;; for debug
(defun rule-is-case-generated (rule)
  (and (is-true? (rule-condition rule))
       (let ((labels (rule-labels rule)))
         (dolist (lb labels nil)
           (let ((lstr (string lb)))
             (when (and (= 2 (length lstr))
                        (string-equal lstr "CA"))
               (return-from rule-is-case-generated t)))))))

(defun print-case-axioms (node)
  (let ((mod (goal-context (ptree-node-goal node)))
        (cas nil))
    (with-in-module (mod)
      (let ((all-rules (module-all-rules mod)))
        (dolist (rule all-rules)
          (when (rule-is-case-generated rule)
            (push rule cas))))
      (when cas
        (format t "~%** generated axioms in goal ~s" (goal-name (ptree-node-goal node)))
        (let ((*print-indent* (+ 2 *print-indent*)))
          (dolist (rl cas)
            (print-next)
            (print-axiom-brief rl)))))))

(defun all-cases ()
  (unless *proof-tree* 
    (with-output-chaos-error ('no-context)
      (format t "No proof tree!")))
  (dag-wfs (ptree-root *proof-tree*)
           #'print-case-axioms))

;;; ======================================
;;; TACTIC: Case Analysis on Sequence [CS]
;;; TODO
;;; ======================================
(defun apply-cs (ptree-node &rest ignore)
  (declare (ignore ignore))
  ptree-node)

;;; ==========================================
;;; INSTANCIATE (non-executable) axiom (:init)
;;; ==========================================

;;; get-target-axiom : module target-form -> {nil | axiom}
;;; target-form : (<kind> <form>)
;;;
(defun get-target-axiom (module target-form &optional (add-to-module nil))
  (let ((kind (first target-form))
        (ax nil))
    (cond ((eq :label kind) (setq ax (get-rule-labelled module (second target-form))))
          (t (with-in-module (module)
               (let ((*chaos-quiet* nil))
                 (setq ax (parse-axiom-declaration (parse-module-element-1 (cdr target-form)))))
               (when add-to-module
                 (set-operator-rewrite-rule module ax)
                 (adjoin-axiom-to-module module ax)
                 (set-needs-rule)))))
    ax))

;;; resolve-subst-form
;;;
(defun resolve-subst-form (context subst-forms &optional (normalize nil))
  (unless subst-forms (return-from resolve-subst-form nil))
  (with-in-module (context)
    (let ((subst nil)
          (*parse-variables* nil))
      (dolist (subst-form subst-forms)
        (let ((var-form (first subst-form))
              (term-form (rest subst-form))
              (var nil)
              (term nil))
          (with-citp-debug ()
            (format t "~%resolving subst form:")
            (print-next)
            (format t " var=~s, term=~s" var-form term-form))
          (let ((*chaos-quiet* nil))
            (setq var (simple-parse context var-form)))
          (when (or (term-is-an-error var) (not (term-is-variable? var)))
            (with-output-chaos-error ('invalid-var-form)
              (format t "Invalid variable in substitution: ~s" var-form)))
          (let ((*chaos-quiet* nil))
            (setq term (simple-parse context term-form)))
          (when (term-is-an-error term)
            (with-output-chaos-error ('invalid-term)
              (format t "No parse..: ~s" term-form)))
          (unless (sort<= (term-sort term) (variable-sort var) *current-sort-order*)
            (with-output-chaos-error ('sort-mismatch)
              (format t "Sort mismatch for the substitution")
              (print-next)
              (format t "  variable: ") (term-print-with-sort var)
              (print-next)
              (format t "  term: ") (term-print-with-sort term)))
          (when normalize
            (with-spoiler-on
              (setq term (normalize-term-in context term))))
          (push (cons var term) subst)))
      subst)))

;;; 
(defun make-real-instanciation-subst (subst axiom-vars)
  (let ((rsubst nil)
        rv)
    (dolist (vt-pair subst)
      (if (setq rv (get-real-target-variable (car vt-pair) axiom-vars))
          (setq rsubst (acons rv (cdr vt-pair) rsubst))
        (with-output-chaos-error ('no-var)
          (format t "Instanciating an axiom, no such variable ")
          (term-print-with-sort (car vt-pair)))))
    rsubst))

;;; make-axiom-instance : module substitution axiom label -> axiom'
;;; terms in resulting axiom must be ground terms.
;;;
(defun make-axiom-instance (module subst axiom &optional (label nil))
  (flet ((make-proper-label (label)
           (if (stringp label)
               (intern label)
             label)))
    (with-in-module (module)
      (let ((new-axiom (rule-copy-canonicalized axiom module)))
        (if subst
            (apply-substitution-to-axiom (make-real-instanciation-subst subst 
                                                                        (axiom-variables new-axiom))
                                         new-axiom 
                                         (if label
                                             (make-proper-label label)
                                           'init)
                                         (if label
                                             nil
                                           t))
          (setf (rule-labels new-axiom) (if label 
                                            (make-proper-label label)
                                          (cons (make-proper-label label) (rule-labels new-axiom)))))
        new-axiom))))

;;; instanciate-axiom
;;; 
(defun instanciate-axiom (goal target-form subst-form &optional (label nil))
  (let* ((*current-module* (goal-context goal))
         (target-axiom (get-target-axiom *current-module* target-form)))
    (instanciate-axiom-in-goal goal target-axiom subst-form label)))

;;; apply-init-tactic : tactic-init -> void
;;; apply :def(ed) :init command to the current goal
;;;
(defun apply-init-tactic (ptree-node &optional (tactic .tactic-init.))
  (declare (type ptree-node ptree-node)
           (type tactic-init tactic))
  (when (goal-is-discharged (ptree-node-goal ptree-node))
    ;; (format t "~%goal is alredy discharged: ~a" (goal-name (ptree-node-goal ptree-node)))
    (return-from apply-init-tactic nil))
  (let ((goal (prepare-next-goal ptree-node tactic))
        (ax (tactic-init-axiom tactic))
        (subst (tactic-init-subst tactic))
        (kind (tactic-init-kind tactic)))
    (setf (goal-targets goal) (goal-targets (ptree-node-goal ptree-node)))
    (instanciate-axiom-in-goal goal ax subst (if (stringp kind)
                                                 kind
                                               nil))
    (values t (list goal))))

;;; supporting function around :init

(defun report-instanciated-axiom (instance)
  (let ((*print-indent* (+ 2 *print-indent*))
        (*print-line-limit* 80))
    (print-next)
    (print-axiom-brief instance)))

(defun introduce-instanciated-axiom-to-module (instance module)
  (with-in-module (module)
    (setf (axiom-kind instance) nil)    ; reset bad flag
    (set-operator-rewrite-rule module instance)
    (adjoin-axiom-to-module module instance)
    (compile-module module t)))

(defun optimize-instanciated-axiom (module instance)
  (with-in-module (module)
    (let ((aax nil))
      ;; case 3:1
      (when (or (is-false? (rule-condition instance))
                (term-equational-equal (rule-lhs instance) (rule-rhs instance)))
        (let ((na (rule-copy-canonicalized instance module (list '|:nonexec| '|3:1|))))
          (push na aax)))
      ;; case 3:2
      (when (and (is-true? (rule-condition instance))
                 (and (not (term-equational-equal (rule-lhs instance) (rule-rhs instance)))
                      (or (is-true? (rule-lhs instance))
                          (is-false? (rule-lhs instance)))))
        (let* ((na (rule-copy-canonicalized instance module (list '|3:2|)))
               (lhs (rule-lhs instance))
               (rhs (rule-rhs instance)))
          (setf (rule-lhs instance) rhs)
          (setf (rule-rhs instance) lhs)
          (push na aax)))
      ;; case 3:3
      (when (and (is-true? (rule-condition instance))
                 (and (not (term-equational-equal (rule-lhs instance) (rule-rhs instance)))
                      (not (or (is-true? (rule-lhs instance))
                               (is-false? (rule-lhs instance))))))
        (let ((na (rule-copy-canonicalized instance module (list '|3:3|))))
          (push na aax)))
      ;; case 3:4
      (when (and (not (or (is-true? (rule-condition instance))
                          (is-false? (rule-condition instance))))
                 (not (term-equational-equal (rule-lhs instance) (rule-rhs instance)))
                 (or (is-true? (rule-lhs instance))
                     (is-false? (rule-lhs instance))))
        (let* ((na (rule-copy-canonicalized instance module (list '|3:4|)))
               (lhs (rule-lhs instance))
               (rhs (rule-rhs instance)))
          (setf (rule-lhs instance) rhs)
          (setf (rule-rhs instance) lhs)
          (push na aax)))
      ;; case 3:5
      (when (and (not (or (is-true? (rule-condition instance))
                          (is-false? (rule-condition instance))))
                 (not (term-equational-equal (rule-lhs instance) (rule-rhs instance)))
                 (not (or (is-true? (rule-lhs instance))
                          (is-false? (rule-lhs instance)))))
        (let ((na (rule-copy-canonicalized instance module (list '|3:5|))))
          (push na aax)))
      (nreverse aax))))

(defun instanciate-axiom-in-goal (goal target-axiom subst-form &optional (label nil))
  (let* ((module (goal-context goal))
         (subst (resolve-subst-form module
                                    subst-form 
                                    (citp-flag citp-normalize-init))))
    (let ((instance (remove-nonexec (make-axiom-instance module subst target-axiom label)))
          (new-axioms nil))
      ;; we normalize the instance
      (with-spoiler-on
          (multiple-value-bind (n-sen applied?)
              (normalize-sentence instance module nil :variable-is-constant)
            (when applied?
              (setf instance n-sen))))
      ;; introduce additional axioms
      (setq new-axioms (optimize-instanciated-axiom module instance))
      ;; input the instance to current context
      (with-in-module (module)
        (when new-axioms
          (setf (goal-assumptions goal) (append (goal-assumptions goal) new-axioms))
          (format t "~%**> initialized the axiom in goal ~s" (goal-name goal))
          (dolist (ax new-axioms)
            (report-instanciated-axiom ax)
            (introduce-instanciated-axiom-to-module ax module)))
        (when-citp-verbose ()
           (pr-goal goal))))))

(defun instanciate-axiom-in-module (module target-axiom subst &optional (label nil))
  (with-in-module (module)
    (let ((instance (remove-nonexec (make-axiom-instance module subst target-axiom label))))
      (format t "~%**> initialized the axiom in module ~a" (get-module-simple-name module))
      (report-instanciated-axiom instance)
      (introduce-instanciated-axiom-to-module instance module))))

;;; ================================
;;; Target sentence T -> A implies T [:imp]
;;; ================================

(defun make-impl-assumption (ax)
  (simplify-eq-form (axiom-lhs ax)))

;;; a imply lhs 
(defun make-impl-form (lhs assumption)
  (make-applform *bool-sort* *bool-imply* 
                 (list (make-impl-assumption assumption) lhs)))

(defun introduce-implication-to-goal (target-form subst-form)
  (let ((target-axiom (get-target-axiom *current-module* target-form t))
        (subst (if subst-form
                   (resolve-subst-form *current-module* subst-form)
                 nil))
        (instance nil)
        (new-targets nil))
    (setq instance (make-axiom-instance *current-module* subst target-axiom))
    (with-next-context (*proof-tree*)
      (unless (and (is-true? (axiom-rhs instance))
                   (is-true? (axiom-condition instance)))
        (with-output-chaos-error ('invalid-axiom)
          (format t "~%[:imp] invalid instance")
          (print-next)
          (print-axiom-brief instance)))
      ;; modify the target sentence.
      ;; instance: eq p = true .
      ;; goal: eq l = r .
      ;; -> new goal eq p implies l = r .
      (dolist (target (goal-targets (ptree-node-goal .context.)))
        (let ((new-lhs (make-impl-form (axiom-lhs target) instance))
              (*print-indent* (+ *print-indent* 2))
              (rtarget (rule-copy-canonicalized target *current-module*)))
          (with-citp-debug ()
            (format t "~%[:imp] target: ")
            (print-axiom-brief target))
          (if (sort= (term-sort (axiom-rhs rtarget)) *bool-sort*)
              (progn
                (push rtarget new-targets)
                (setf (axiom-lhs rtarget) new-lhs
                      (axiom-labels rtarget) (cons :imp (axiom-labels rtarget)))
                (format t "~%[:imp] target sentence is converted...")
                (print-next)
                (princ "=> ")
                (print-next)
                (print-axiom-brief rtarget))
            (with-output-chaos-warning ()
              (format t "[:imp] sort of target sentence is not Bool. Ignored.")
              (print-next)
              (print-axiom-brief target)))))
      (setf (goal-targets (ptree-node-goal .context.)) (nreverse new-targets)))))

;;; ==============
;;; CRITICAL PAIRS [:cp]
;;; ==============

(defun citp-rename-term-variables (suffix list-vars)
  (let ((done nil))
    (dolist (var list-vars)
      (unless (member var done)
        (push var done)
        (setf (variable-name var) (intern (format nil "~a~a" (variable-name var) suffix)))))))

(declaim (type fixnum *renamed-variable-number*))
(defvar *renamed-variable-number* 0)
(let ((*renamed-variable-number* 0))
  (declare (type fixnum *renamed-variable-number*)
           (special *renamed-variable-number*))
  (defun citp-rename-axiom-variables (axiom)
    (citp-rename-term-variables (incf *renamed-variable-number*) (axiom-variables axiom))
    axiom)
)

(defstruct (cpp (:print-function pr-cpp))
  (t1 nil :type term)                   ; sigma(lhs[pos])
  (t2 nil :type term)                   ; sigma(lhs)
  (pos nil :type list)                  ; occurence of t1 in root term
  (subst nil :type list)                ; mgu
  (cpairs nil :type list))              ; generated critical pairs in a form of axiom

(defun pr-cpp (cpp &optional (stream *standard-output*) &rest ignore)
  (declare (ignore ignore))
  (format stream "~%Critical Pair ---------")
  (let ((*print-indent* (+ *print-indent*))
        (*standard-output* stream))
    (print-next)
    (princ "term 1: ") (term-print-with-sort (cpp-t1 cpp))
    (print-next)
    (princ "term 2: ") (term-print-with-sort (cpp-t2 cpp))
    (print-next)
    (format t "position: ~a" (cpp-pos cpp))
    (print-next)
    (princ "substitution: ") (print-substitution (cpp-subst cpp))
    (when (cpp-cpairs cpp)
      (setq *print-indent* (+ 2 *print-indent*))
      (format t "~%- ~d critical pairs" (length (cpp-cpairs cpp)))
      (dolist (cpair (cpp-cpairs cpp))
        (print-next)
        (print-axiom-brief cpair)))))

(defun compute-overwraps (t1 t2 occur)
  (let ((cpps nil))
    (cond ((term-is-applform? t1)
           (multiple-value-bind (subst no-match e-eq)
               (unify t1 t2)
             (declare (ignore e-eq))
             (unless no-match
               (push (make-cpp :t1 (substitution-image-simplifying subst t1)
                               :t2 (substitution-image-simplifying subst t2)
                               :subst subst
                               :pos occur) cpps))
             (let ((pos 0))
               (declare (type fixnum pos))
               (dolist (sub (term-subterms t1))
                 (setq cpps (append cpps (compute-overwraps sub t2 (append occur (cons pos occur)))))
                 (incf pos)))))
          (t nil))
    cpps))

(defun term-at-pos (pos term)
  (if pos
      (term-at-pos (cdr pos) (term-arg-n term (car pos)))
    term))

(defun replace-term-at (pos term repl-term)
  (let ((target (term-at-pos pos term)))
    (term-replace target repl-term)
    term))

;;; compute-all-overwrapps : axiom axiom -> List(cpp)
;;;
(defun compute-axiom-overwrapps (ax-1 ax-2)
    (let ((lhs-1 (rule-lhs ax-1))
          (lhs-2 (rule-lhs ax-2))
          (cpps nil))
      (setq cpps (compute-overwraps lhs-1 lhs-2 '()))
      cpps))

(defun generate-critical-pairs (cpps ax-1 ax-2)
  (dolist (cpp cpps)
    (let ((subst (cpp-subst cpp))
          (cpairs nil))
      (let ((cond-1 (substitution-image-simplifying subst (rule-condition ax-1)))
            (cond-2 (substitution-image-simplifying subst (rule-condition ax-2)))
            (rhs (substitution-image-simplifying subst (rule-rhs ax-1)))
            (lhs (replace-term-at (cpp-pos cpp)
                                  (substitution-image-simplifying subst (axiom-lhs ax-1))
                                  (substitution-image-simplifying subst (axiom-rhs ax-2)))))
        (with-citp-debug ()
          (format t "~%cond-1: ")(term-print-with-sort cond-1)
          (format t "~%cond-2: ")(term-print-with-sort cond-2)
          (format t "~%lhs: ") (term-print-with-sort lhs)
          (format t "~%rhs: ") (term-print-with-sort rhs))

        (let ((*perform-on-demand-reduction* t))
          (compile-module *current-module* t)
          ;; LHS
          (rewrite lhs *current-module*)
          ;; RHS
          (rewrite rhs *current-module*)
          (unless (term-equational-equal lhs rhs)
            (let ((ordered-pair (sort (list lhs rhs) #'lrpo)))
              (pushnew (make-rule :lhs (first ordered-pair)
                                  :rhs (second ordered-pair)
                                  :condition *bool-true*
                                  :type :equation ; might be changed later by command :equqtion or :rule
                                  :labels '(cp))
                       cpairs
                       :test #'rule-is-similar?)))

          ;; Condition
          (let ((new-cond (make-applform *condition-sort* *bool-cond-op* (list cond-1 cond-2))))
            (with-citp-debug ()
              (format t "~%[cp] generated condition: ")
              (term-print-with-sort new-cond))
            (rewrite new-cond *current-module*)
            (with-citp-debug ()
              (format t "~%     after normalized :")
              (print-next)
              (term-print-with-sort new-cond))
            (unless (is-true? new-cond)
              (cond ((eq *bool-cond-op* (term-head new-cond))
                     (let ((subs (list-assoc-subterms new-cond *bool-cond-op*)))
                       (setq subs (sort subs #'lrpo))
                       (do* ((sl subs (cdr sl))
                             (lhs (car sl) (car sl))
                             (rhs (cadr sl)))
                           ((null rhs))
                         (pushnew (make-rule :lhs lhs
                                             :rhs rhs
                                             :condition *bool-true*
                                             :type :equation
                                             :labels '(cpc))
                                  cpairs
                                  :test #'rule-is-similar?))))
                    (t  (pushnew (make-rule :lhs new-cond
                                            :rhs *bool-true*
                                            :condition *bool-true*
                                            :type :equation
                                            :labels '(cpc))
                                 cpairs
                                 :test #'rule-is-similar?)))))))
      (setf (cpp-cpairs cpp) cpairs))))

(defun compute-critical-pairs (module axiom1 axiom2)
  (with-in-module (module)
    (let ((ax-1 (citp-rename-axiom-variables (rule-copy-canonicalized axiom1 module)))
          (ax-2 (citp-rename-axiom-variables (rule-copy-canonicalized axiom2 module)))
          (cpp-1 nil)
          (cpp-2 nil))
      (setq cpp-1 (compute-axiom-overwrapps ax-1 ax-2))
      (setq cpp-2 (compute-axiom-overwrapps ax-2 ax-1))
      (generate-critical-pairs cpp-1 ax-1 ax-2)
      (generate-critical-pairs cpp-2 ax-2 ax-1)

      (with-citp-debug ()
        (format t "~%------- cpp-1")
        (print cpp-1)
        (format t "~%------- cpp-2")
        (print cpp-2))
      
      (let ((all-cpairs nil))
        (dolist (cp1 (nconc cpp-1 cpp-2))
          (setq all-cpairs (nconc all-cpairs (cpp-cpairs cp1))))
        (remove-duplicates all-cpairs :test #'rule-is-similar?)))))

;;; apply-cp : axiom-form axiom-form -> void
;;;
(defun apply-cp (target-1 target-2)
  (let ((context (get-next-proof-context *proof-tree*)))
    (unless context
      (with-output-chaos-error ('no-context)
        (format t "Applying [cp], no context module is established.")))
    (let ((goal (ptree-node-goal context)))
      (with-in-module ((goal-context goal))
        (let ((t1axiom (get-target-axiom *current-module* target-1))
              (t2axiom (get-target-axiom *current-module* target-2))
              (cpps nil))
          (setq cpps
            (setf (goal-critical-pairs goal) (compute-critical-pairs *current-module* t1axiom t2axiom)))
          (when cpps
            (format t "~%[cp] :")
            (let ((*print-indent* (+ 2 *print-indent*)))
              (dotimes (x (length cpps))
                (print-next)
                (format t "(~d) " (1+ x))
                (let ((ax (nth x cpps)))
                  (term-print-with-sort (axiom-lhs ax))
                  (print-next)
                  (princ "    => ")
                  (term-print-with-sort (axiom-rhs ax)))))))))))

;;; add-critical-pairs
;;;
(defun add-critical-pairs (type direction)
  (let ((context (get-next-proof-context *proof-tree*)))
    (unless context
      (with-output-chaos-error ('no-context)
        (format t "Applying [cp], no context module is established.")))
    (let ((goal (ptree-node-goal context))
          (applied nil))
      (with-in-module ((goal-context goal))
        (dolist (cps (goal-critical-pairs goal))
          (setf (rule-type cps) type)
          (when (eq direction :backward)
            (let ((rhs (rule-lhs cps))
                  (lhs (rule-rhs cps)))
              (setf (rule-lhs cps) lhs
                    (rule-rhs cps) rhs)))
          (compute-rule-method cps)
          (set-operator-rewrite-rule *current-module* cps)
          (adjoin-axiom-to-module *current-module* cps)
          (setq applied (nconc applied (list cps))))
        (when applied
          (setf (goal-assumptions goal) (nconc (goal-assumptions goal) (nreverse applied)))
          (format t "~%[cp] added cp ~a~p to goal ~s: " type (length applied) (goal-name goal))
          (let ((*print-indent* (+ 2 *print-indent*)))
            (dolist (ax applied)
              (print-next)
              (print-axiom-brief ax)))
          (when *citp-verbose*
            (pr-goal goal)))))))

;;; ===================================================
;;; {:red | :exec | :bred} [in <goal-name> : ] <term> .
;;; ===================================================
;;; reduce-in-goal : List( mode goal-name token-seq)
;;;
(defun reduce-in-goal (mode goal-name token-seq)
  (with-citp-debug ()
    (format t "~%~s in ~s : ~s" (string mode) goal-name token-seq))
  (let ((next-goal-node (get-target-goal-node goal-name)))
    ;; do rewriting
    (perform-reduction* token-seq (goal-context (ptree-node-goal next-goal-node)) mode)))

;;; ===========
;;; TACTIC: :NF
;;; explicit application of NF (compute normal form of targets).
;;; 
;;; ===========
(defun apply-nf (ptree-node &rest ignore)
  (declare (type ptree-node ptree-node)
           (ignore ignore))
  (let ((.cur-goal. (ptree-node-goal ptree-node)))
    (when (goal-is-discharged .cur-goal.)
      (with-output-chaos-warning ()
        (format t "** The goal ~s has already been proved!."
                (goal-name .cur-goal.)))
      (return-from apply-nf nil))
    (with-citp-env ()
      (with-spoiler-on ()
        (with-in-module ((goal-context .cur-goal.))
        (let ((n-targets nil)
              (applied nil))
          ;; normalize goal sentences
          (dolist (sen (goal-targets .cur-goal.))
            (multiple-value-bind (ngoal app?)
                (normalize-sentence sen *current-module*)
              (if app?
                  (progn (setq applied t) (push ngoal n-targets))
                (push sen n-targets))))
          (when applied
            (let ((next-goal (prepare-next-goal ptree-node 'nf)))
              (setf (goal-targets next-goal) (nreverse n-targets))
              (return-from apply-nf (values t (list next-goal)))))
          (values nil nil)))))))

;;; ===========
;;; TACTIC: :CT
;;; do contradiction check, can dischage the goal
;;; ===========
(defun apply-ct (ptree-node &rest ignore)
  (declare (type ptree-node ptree-node)
           (ignore ignore))
  (let ((.cur-goal. (ptree-node-goal ptree-node)))
    (when (goal-is-discharged .cur-goal.)
      (with-output-chaos-warning ()
        (format t "** The goal ~s has already been proved!."
                (goal-name .cur-goal.)))
      (return-from apply-ct nil))
    ;;
    (with-in-module ((goal-context .cur-goal.))
      (with-citp-env ()
        (with-spoiler-on ()
          (when (check-contradiction .cur-goal. 'ct)
            (with-in-module ((goal-context .cur-goal.))
              (format t "~%[ct] dischaged:")
              (dolist (target (goal-targets .cur-goal.))
                (print-next)
                (print-axiom-brief target))
              (setf (goal-proved .cur-goal.) (goal-targets .cur-goal.))
              (setf (goal-targets .cur-goal.) nil)))))
      t)))

;;; ==============
;;; :ctf or :ctf-
;;; ==============
(defvar .pvar-names. nil)

(defun make-ctf-constructor-pattern (goal const-op)
  (let ((arity (method-arity const-op)))
    (cond (arity
           (let ((args nil)
                 (form nil))
             (dolist (s arity)
               (let ((pn (assoc s .pvar-names. :test #'eq)))
                 (unless pn 
                   (setq pn (cons s 0))
                   (push pn .pvar-names.))
                 (push (intro-fresh-constant goal 
                                             (if (zerop (cdr pn))
                                                 (progn (incf (cdr pn))
                                                        "CTF")
                                               (format nil "CTF-~d" (incf (cdr pn))))
                                             s)
                       args)))
             (setq form (make-applform (method-coarity const-op)
                                       const-op
                                       (nreverse args)))
             (with-citp-debug ()
               (with-in-module ((goal-context goal))
                 (format t "~%[ctf consructor] ")
                 (term-print-with-sort form)))
             form))
          (t (make-applform (method-coarity const-op) const-op nil)))))

(defun do-apply-ctf-with-constructors (cur-node term tactic)
  (let ((cur-goal (ptree-node-goal cur-node))
        (sort (term-sort term))
        (goals nil))
    (let ((constructors (get-constructors-of-sort sort *current-module*))
          (.pvar-names. nil))
      (declare (special .names.))
      (unless constructors
        (with-output-chaos-error ('no-constructors)
          (format t "Sort ~a has no constructors." (sort-name sort))))
      (dolist (const constructors)
        (let ((n-goal nil)
              (const-pat nil)
              (.pvar-names. nil))
          (setq n-goal (prepare-next-goal cur-node tactic))
          (setq const-pat (make-ctf-constructor-pattern n-goal const))
          (with-in-module ((goal-context n-goal))
            (multiple-value-bind (lhs rhs type)
                (if (sort= (term-sort term) *bool-sort*)
                    (simplify-boolean-axiom term const-pat)
                  (values term const-pat :equation))
              (when lhs
                (let ((ax (make-rule :lhs lhs
                                     :rhs rhs
                                     :condition *bool-true*
                                     :type type
                                     :labels (list (tactic-name tactic))
                                     :behavioural nil)))
                  (adjoin-axiom-to-module *current-module* ax)
                  (set-operator-rewrite-rule *current-module* ax)
                  (compile-module *current-module*)
                  (push n-goal goals)
                  (setf (goal-targets n-goal) (goal-targets cur-goal))
                  (setf (goal-assumptions n-goal)
                    (append (goal-assumptions cur-goal) (list ax)))))))))
      (with-citp-debug ()
        (format t "~%[ctf] constructors generated:")
        (dolist (g (reverse goals))
          (print-next)
          (pr-goal g)))
      (if goals
          (values t (nreverse goals))
        (values nil nil)))))

(defun do-apply-ctf-to-equation (cur-node equation tactic)
  (let ((cur-goal (ptree-node-goal cur-node)))
    (flet ((add-assumption (goal lhs rhs)
             (let (n-axiom)
               (multiple-value-bind (n-lhs n-rhs type)
                   (simplify-boolean-axiom lhs rhs)
                 (cond (n-lhs
                        (setq n-axiom (make-rule :lhs n-lhs
                                                 :rhs n-rhs
                                                 :condition *bool-true*
                                                 :type type
                                                 :behavioural nil
                                                 :labels (list(tactic-name tactic))))
                        (with-in-module ((goal-context goal))
                          (adjoin-axiom-to-module *current-module* n-axiom)
                          (set-operator-rewrite-rule *current-module* n-axiom)
                          (compile-module *current-module*))
                        (setf (goal-targets goal) (goal-targets cur-goal))
                        (setf (goal-assumptions goal) 
                          (append (goal-assumptions cur-goal) (list n-axiom))))
                       (t
                        (with-output-chaos-warning ()
                          (format t "[ctf] invalid assumption")
                          (print-next)
                          (print-axiom-brief equation)
                          (print-next)
                          (format t "...ignored.")
                          nil)))))))
      (let ((t-goal (prepare-next-goal cur-node tactic))
            (f-goal (prepare-next-goal cur-node tactic)))
        (with-in-module ((goal-context cur-goal))
          (let ((lhs (make-applform *bool-sort* 
                                    *eql-op*
                                    (list (rule-lhs equation) 
                                          (rule-rhs equation)))))
            ;; true case
            (unless (add-assumption t-goal lhs *bool-true*)
              (setq t-goal nil))
            ;; false case
            (unless (add-assumption f-goal lhs *bool-false*)
              (setq f-goal nil))))
        (with-citp-debug ()
          (format t "~%citp from equation: generated")
          (print-next)
          (when t-goal
            (pr-goal t-goal))
          (when f-goal
            (pr-goal f-goal)))
        (if (and t-goal f-goal)
            (values t (list t-goal f-goal))
          (if t-goal
              (values t (list t-goal))
            (if f-goal
                (values t (list f-goal))
              (values nil nil))))))))

(defun parse-axiom-or-term (form term?)
  (let ((*chaos-quiet* nil))
    (if term?
        (let ((*parse-variables* nil))
          (let ((res (simple-parse *current-module* form *cosmos*)))
            res))
      (parse-axiom-declaration (parse-module-element-1 form)))))

(defun do-apply-ctf (cur-node term-or-equation &optional (tactic .tactic-ctf.))
  (with-citp-env ()
    (let ((cur-goal (ptree-node-goal cur-node)))
      (when (already-proved? cur-goal)
        (return-from do-apply-ctf nil))
      (if (term? term-or-equation)
          (do-apply-ctf-with-constructors cur-node term-or-equation tactic)
        (do-apply-ctf-to-equation cur-node term-or-equation tactic)))))

;;; :ctf(-) toplevel function
;;;
(defun apply-ctf (s-form term? dash? &optional (verbose *citp-verbose*))
  (let ((ptree-node (get-next-proof-context *proof-tree*)))
    (with-in-module ((goal-context (ptree-node-goal ptree-node)))
      (with-citp-env ()
        (let ((form (parse-axiom-or-term s-form term?)))
          (multiple-value-bind (applied next-goals)
              (do-apply-ctf ptree-node form)
            (declare (ignore applied))
            (unless next-goals
              (return-from apply-ctf nil))
            (format t "~%** Generated ~d goal~p" (length next-goals) (length next-goals))
            (when *citp-spoiler*
              ;; apply implicit rd
              (dolist (ngoal next-goals)
                (do-apply-rd ngoal nil dash? .tactic-ctf.)))
            ;; add generated nodes as children
            (add-ptree-children ptree-node next-goals)
            (when verbose
              (dolist (gn (ptree-node-subnodes ptree-node))
                (pr-goal (ptree-node-goal gn))))
            (ptree-node-subnodes ptree-node)))))))
      
;;;=====================
;;; :defined :ctf, :ctf-
;;;=====================
(defun apply-ctf-tactic (ptree-node tactic)
  (declare (type ptree-node ptree-node)
           (type tactic-ctf tactic))
  (let ((goal (ptree-node-goal ptree-node)))
    (with-in-module ((goal-context goal))
       (multiple-value-bind (applied next-goals)
           (do-apply-ctf ptree-node (tactic-ctf-form tactic) tactic)
         (declare (ignore applied))
         (unless next-goals
           (return-from apply-ctf-tactic nil))
         (when *citp-spoiler*
           ;; apply implicit rd
           (dolist (ngoal next-goals)
             (do-apply-rd ngoal nil (tactic-ctf-minus tactic) tactic)))

         (values t next-goals)))))

;;;==============
;;; :csp or :csp-
;;;==============
(defun do-apply-csp (cur-node axs &optional (tactic .tactic-csp.))
  (unless (already-proved? cur-node)
    (let ((cur-goal (ptree-node-goal cur-node))
          (ngoals nil))
      ;; add given assumptions with generating child nodes
      (dolist (ax (mapcar #'(lambda (x) 
                              (rule-copy-canonicalized x (goal-context cur-goal) (list (tactic-name tactic))))
                          axs))
        (let ((n-goal (prepare-next-goal cur-node tactic)))
          (with-in-module ((goal-context n-goal))
            (adjoin-axiom-to-module *current-module* ax)
            (set-operator-rewrite-rule *current-module* ax)
            (compile-module *current-module*))
          (setf (goal-targets n-goal) (goal-targets cur-goal))
          (setf (goal-assumptions n-goal) (append (goal-assumptions cur-goal) (list ax)))
          (push n-goal ngoals)))
      (with-citp-debug ()
        (format t "~%~a generated:" (tactic-name tactic))
        (dolist (g (reverse ngoals))
          (print-next)
          (pr-goal g)))
      (values t (nreverse ngoals)))))

(defun apply-csp (ax-forms dash? &optional (verbose *citp-verbose*))
  (let ((ptree-node (get-next-proof-context *proof-tree*)))
    (with-in-module ((goal-context (ptree-node-goal ptree-node)))
      (with-citp-env ()
        (let ((axs nil))
          (dolist (ax ax-forms)
            (let ((*chaos-quiet* nil))
              (push (parse-axiom-declaration (parse-module-element-1 ax)) axs)))
          (multiple-value-bind (applied next-goals)
              (do-apply-csp ptree-node (nreverse axs))
            (declare (ignore applied))
            (unless next-goals
              (return-from apply-csp nil))
            (format t "~%** Generated ~d goal~p" (length next-goals) (length next-goals))
            (when-spoiler-on ()
              ;; apply implicit rd
              (dolist (ngoal next-goals)
                (do-apply-rd ngoal nil dash? .tactic-csp.)))
            ;; add generated node as children
            (add-ptree-children ptree-node next-goals)
            (when verbose
              (dolist (gn (ptree-node-subnodes ptree-node))
                (pr-goal (ptree-node-goal gn))))
            (ptree-node-subnodes ptree-node)))))))

;;;=====================
;;; :defined :csp, :csp-
;;;=====================
(defun apply-csp-tactic (ptree-node tactic)
  (declare (type ptree-node ptree-node)
           (type tactic-csp tactic))
  (let ((goal (ptree-node-goal ptree-node)))
    (with-in-module ((goal-context goal))
      (with-citp-env ()
        (multiple-value-bind (applied next-goals)
            (do-apply-csp ptree-node (tactic-csp-forms tactic) tactic)
          (declare (ignore applied))
          (unless next-goals
            (return-from apply-csp-tactic nil))
          (when-spoiler-on ()
            ;; apply implicit rd
            (dolist (ngoal next-goals)
              (do-apply-rd ngoal nil (tactic-csp-minus tactic) tactic)))
          (values t next-goals))))))

;;;
;;; use discharged sentences as axioms
;;;
(defun use-discharged-goals (list-labels)
  (with-next-context (*proof-tree*)
    (let ((goal (ptree-node-goal .context.))
          (axs (find-discharged-sentences-with-label list-labels)))
      (use-sentences-in-goal goal axs))))

;;;
;;; use-theory
;;;
(defun use-theory (label theory)
  (with-next-context (*proof-tree*)
    (let ((goal (ptree-node-goal .context.))
          (ax (get-discharged-sentence-with-label label)))
      (use-theory-in-goal goal ax theory))))

;;;
;;; embed-discharged-goals : list-labels module-name -> embeded module
;;;
(defun embed-discharged-goals (list-labels module-name into)
  (let ((axs (find-discharged-sentences-with-label list-labels))
        (emod (if into
                  (eval-modexp module-name)
                (make-embed-module module-name (get-context-module)))))
    (unless emod
      (with-output-chaos-error ()
        (format t "No such module ~a" module-name)))
    (embed-sentences-in-module emod axs)
    emod))

;;;
;;; embed-theory
;;;
(defun embed-theory (label theory module-name into)
  (let ((ax (get-discharged-sentence-with-label label))
        (emod (if into
                  (eval-modexp module-name)
                (make-embed-module module-name (get-context-module)))))
    (unless emod
      (with-output-chaos-error ()
        (format t "[:embed] No such module ~a" module-name)))
    (embed-theory-in-module emod (term-head (axiom-lhs (car ax))) theory)
    emod))

;;; -----------------------------------------------------------
;;; report-citp-stat
;;;
(defun report-citp-stat ()
  (when *show-stats*
    (format t "~%~a" (generate-statistics-form-rewriting-only))))

;;; ******
;;; :apply
;;; ******

;;; APPLY-TACTIC
;;; apply-tactic : ptree-node tactic -> List(ptree-node)
;;; returns the list of generated goal nodes.
;;;
(defun apply-tactic (ptree-node tactic &optional (verbose nil))
  (declare (type ptree-node ptree-node)
           (type tactic tactic))
  (flet ((prepare-goal-context (module)
           (compile-module module)
           (reset-term-memo-table module)))
    (with-citp-env ()
      (when (goal-is-discharged (ptree-node-goal ptree-node))
        (with-output-chaos-warning ()
          (format t "** The goal ~s has already been proved!." (goal-name (ptree-node-goal ptree-node)))
          (return-from apply-tactic nil)))
      (format t "~%[~a]=> :goal{~a}" (tactic-name tactic) (goal-name (ptree-node-goal ptree-node)))
      (initialize-ptree-node ptree-node)
      (prepare-goal-context (goal-context (ptree-node-goal ptree-node)))
      (with-citp-debug ()
        (let ((exe (tactic-executor tactic)))
          (format t "~%Funcalling ~a" exe)))
      (multiple-value-bind (applied next-goals)
          (funcall (tactic-executor tactic) ptree-node tactic)
        (declare (type (or null t) applied)
                 (type list next-goals))
        (unless applied (return-from apply-tactic nil))
        (unless next-goals
          ;; reset the current ptree-node status,
          ;; i.e., cancel side effects
          (initialize-ptree-node ptree-node)
          (return-from apply-tactic nil))
        (format t "~%** Generated ~d goal~p" (length next-goals) (length next-goals))
        (add-ptree-children ptree-node next-goals)
        (when verbose
          (dolist (gn (ptree-node-subnodes ptree-node))
            (pr-goal (ptree-node-goal gn))))
        (ptree-node-subnodes ptree-node)))))

;;; apply-tactics-to-node
;;;
(defun apply-tactics-to-node (target-node tactics &optional (verbose *citp-verbose*))
  (declare (type ptree-node target-node))
  (unless tactics (return-from apply-tactics-to-node nil))
  (let ((subs (apply-tactic target-node (car tactics) verbose)))
    (if subs
        (dolist (target subs)
          (apply-tactics-to-node target (cdr tactics) verbose))
      (apply-tactics-to-node target-node (cdr tactics) verbose))))

;;; apply-tactic-seq
;;; user defined sequence of tactic
;;;
(defun apply-tactic-seq (ptree-node tactic &optional (verbose *citp-verbose*))
  (declare (type ptree-node ptree-node)
           (type tactic-seq tactic))
  (apply-tactics-to-node ptree-node (tactic-seq-tactics tactic) verbose))

;;; apply-tactics 
;;;
(defun flatten-tactic-seq (tactics)
  (let ((res nil))
    (dolist (tactic tactics)
      (if (tactic-seq-p tactic)
          (setq res (nconc res (flatten-tactic-seq (tactic-seq-tactics tactic))))
        (setq res (nconc res (list tactic)))))
    res))

(defun apply-tactics (ptree tactics &optional (verbose *citp-verbose*))
  (declare (type ptree ptree)
           (type list tactics))
  (let ((target (get-next-proof-context ptree)))
    (unless target
      (format t "~%**> All goals have been proved!")
      (return-from apply-tactics nil))
    (clear-term-memo-table *term-memo-table*)
    (reset-rewrite-counters)
    (begin-rewrite)
    (apply-tactics-to-node target (flatten-tactic-seq tactics) verbose)
    (end-rewrite)
    (report-citp-stat)
    (check-success ptree)))

;;; apply-auto
;;;
(defun apply-auto (ptree &optional (tactics .default-tactics.) (verbose *citp-verbose*))
  (with-citp-env ()
    (with-spoiler-on ()
      (reset-rewrite-counters)
      (begin-rewrite)
      (if (next-proof-target-is-specified?)
          (apply-tactics-to-node (get-next-proof-context ptree) tactics verbose)
        (let ((target-nodes (get-unproved-nodes ptree)))
          (unless target-nodes
            (format t "~%**> All goals have been proved!")
            (return-from apply-auto nil))
          (dolist (tactic tactics)
            (dolist (target-node (get-unproved-nodes ptree))
              (apply-tactic target-node tactic verbose)))))
      (end-rewrite)
      (report-citp-stat)
      (check-success ptree))))

;;; apply-tactics-to-goal
;;;
(defun apply-tactics-to-goal (ptree name tactics &optional (verbose *citp-verbose*))
  (let ((target-node (find-goal-node ptree name)))
    (unless target-node
      (with-output-chaos-error ('no-named-goal)
        (format t "There is no goal with name ~s." name)))
    (reset-rewrite-counters)
    (begin-rewrite)
    (apply-tactics-to-node target-node tactics verbose)
    (end-rewrite)
    (report-citp-stat)
    (check-success ptree)))

;;; EOF
